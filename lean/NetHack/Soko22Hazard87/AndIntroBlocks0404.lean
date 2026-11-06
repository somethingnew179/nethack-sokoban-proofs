import NetHack.Soko22Hazard87.AndIntroBlocks0403
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro101000 (p : Pattern) (ha : d310035 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310030 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100999 q ha hb
    | true =>
      simp only [d310030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310031 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310032 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310033 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310034 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310035 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101001 (p : Pattern) (ha : d310041 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310036 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101000 q ha hb
    | true =>
      simp only [d310036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310037 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310038 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310039 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310040 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310041 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101002 (p : Pattern) (ha : d310047 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310042 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101001 q ha hb
    | true =>
      simp only [d310042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310043 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310044 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310045 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310046 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310047 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101003 (p : Pattern) (ha : d310053 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d310048 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101002 q ha hb
    | true =>
      simp only [d310048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d310049 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d310049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d310050 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d310050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d310051 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d310051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d310052 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d310052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d310053 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d310053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101004 (p : Pattern) (ha : d357440 p = 1) (hb : d366182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366180 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53652 q = 1) (hb : d366181 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d366181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d366181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d357439 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d357440 q = 1) (hb : d366182 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d357440, d366182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357440, d366182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro101005 (p : Pattern) (ha : d357556 p = 1) (hb : d366188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d357466 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357467 q = 1) (hb : d366183 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d357467, d366183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101004 q ha hb
    | true =>
      simp only [d357467, d366183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d357494 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d357495 q = 1) (hb : d366184 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d357495, d366184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357495, d366184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d357523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d357524 q = 1) (hb : d366185 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d357524, d366185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357524, d366185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d357553 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357554 q = 1) (hb : d366186 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d357554, d366186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357554, d366186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d309722 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d357555 q = 1) (hb : d366187 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d357555, d366187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d357555, d366187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d357556 q = 1) (hb : d366188 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d357556, d366188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d357556, d366188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101006 (p : Pattern) (ha : d357562 p = 1) (hb : d366194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357557 q = 1) (hb : d366189 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d357557, d366189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101005 q ha hb
    | true =>
      simp only [d357557, d366189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357558 q = 1) (hb : d366190 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d357558, d366190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357558, d366190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357559 q = 1) (hb : d366191 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d357559, d366191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357559, d366191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357560 q = 1) (hb : d366192 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d357560, d366192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357560, d366192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357561 q = 1) (hb : d366193 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d357561, d366193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357561, d366193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357562 q = 1) (hb : d366194 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d357562, d366194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357562, d366194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101007 (p : Pattern) (ha : d357568 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357563 q = 1) (hb : d366195 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d357563, d366195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101006 q ha hb
    | true =>
      simp only [d357563, d366195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357564 q = 1) (hb : d366196 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d357564, d366196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357564, d366196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357565 q = 1) (hb : d366197 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d357565, d366197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357565, d366197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357566 q = 1) (hb : d366198 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d357566, d366198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357566, d366198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357567 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d357567, d366199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357567, d366199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d357568 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101008 (p : Pattern) (ha : d357574 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357569 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101007 q ha hb
    | true =>
      simp only [d357569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357570 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357571 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357572 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357573 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357574 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101009 (p : Pattern) (ha : d357580 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357575 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101008 q ha hb
    | true =>
      simp only [d357575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357576 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357577 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357578 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357579 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357580 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101010 (p : Pattern) (ha : d357586 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357581 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101009 q ha hb
    | true =>
      simp only [d357581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357582 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357583 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357584 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357585 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357586 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101011 (p : Pattern) (ha : d357592 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357587 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101010 q ha hb
    | true =>
      simp only [d357587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357588 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357589 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357590 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357591 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357592 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101012 (p : Pattern) (ha : d357598 p = 1) (hb : d366199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d357593 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101011 q ha hb
    | true =>
      simp only [d357593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d357594 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d357594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d357595 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d357595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d357596 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d357596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d357597 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d357597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d357598 q = 1) (hb : d366199 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d357598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101013 (p : Pattern) (ha : d10054 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2005 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2006 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d10054 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro101014 (p : Pattern) (ha : d32698 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2002 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32698 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101015 (p : Pattern) (ha : d44444 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101014 q ha hb
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101013 q ha hb
  have h3 (q : Pattern) (ha : d35373 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44441 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44442 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44443 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44444 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101016 (p : Pattern) (ha : d44459 p = 1) (hb : d271214 p = 1) : d350949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101014 q ha hb
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101013 q ha hb
  have h3 (q : Pattern) (ha : d35373 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44441 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44442 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44443 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44458 q = 1) (hb : d271214 q = 1) : d44458 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d44459 q = 1) (hb : d271214 q = 1) : d350949 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44459, d350949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44459, d350949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101017 (p : Pattern) (ha : d44465 p = 1) (hb : d271214 p = 1) : d350955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44449 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44462 q = 1) (hb : d271214 q = 1) : d350952 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d44463 q = 1) (hb : d271214 q = 1) : d350953 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44464 q = 1) (hb : d271214 q = 1) : d350954 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d350954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d350954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44465 q = 1) (hb : d271214 q = 1) : d350955 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44465, d350955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44465, d350955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101018 (p : Pattern) (ha : d44467 p = 1) (hb : d271214 p = 1) : d350957 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44462 q = 1) (hb : d271214 q = 1) : d350952 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44463 q = 1) (hb : d271214 q = 1) : d350953 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44464 q = 1) (hb : d271214 q = 1) : d350954 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d350954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d350954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44466 q = 1) (hb : d271214 q = 1) : d350956 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, d350956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44466, d350956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44467 q = 1) (hb : d271214 q = 1) : d350957 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44467, d350957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44467, d350957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101019 (p : Pattern) (ha : d44477 p = 1) (hb : d271214 p = 1) : d350961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44462 q = 1) (hb : d271214 q = 1) : d350952 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44463 q = 1) (hb : d271214 q = 1) : d350953 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44466 q = 1) (hb : d271214 q = 1) : d350956 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, d350956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44466, d350956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44476 q = 1) (hb : d271214 q = 1) : d44476 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d44477 q = 1) (hb : d271214 q = 1) : d350961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44477, d350961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44477, d350961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101020 (p : Pattern) (ha : d44484 p = 1) (hb : d271214 p = 1) : d350968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44468 q = 1) (hb : d271214 q = 1) : d350958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d350958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101017 q ha hb
    | true =>
      simp only [d44468, d350958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101018 q ha hb
  have h2 (q : Pattern) (ha : d44469 q = 1) (hb : d271214 q = 1) : d350959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d350959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d350959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44470 q = 1) (hb : d271214 q = 1) : d350960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d350960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d350960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44478 q = 1) (hb : d271214 q = 1) : d350962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101018 q ha hb
    | true =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101019 q ha hb
  have h5 (q : Pattern) (ha : d44479 q = 1) (hb : d271214 q = 1) : d350963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44480 q = 1) (hb : d271214 q = 1) : d350964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44481 q = 1) (hb : d271214 q = 1) : d350965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d350965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, d350965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44482 q = 1) (hb : d271214 q = 1) : d350966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, d350966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44482, d350966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44483 q = 1) (hb : d271214 q = 1) : d350967 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44483, d350967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44483, d350967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44484 q = 1) (hb : d271214 q = 1) : d350968 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44484, d350968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44484, d350968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro101021 (p : Pattern) (ha : d44488 p = 1) (hb : d271214 p = 1) : d350972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44478 q = 1) (hb : d271214 q = 1) : d350962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101018 q ha hb
    | true =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101019 q ha hb
  have h2 (q : Pattern) (ha : d44479 q = 1) (hb : d271214 q = 1) : d350963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44480 q = 1) (hb : d271214 q = 1) : d350964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44482 q = 1) (hb : d271214 q = 1) : d350966 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, d350966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44482, d350966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44487 q = 1) (hb : d271214 q = 1) : d350971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44487, d350971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44487, d350971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44488 q = 1) (hb : d271214 q = 1) : d350972 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44488, d350972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44488, d350972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101022 (p : Pattern) (ha : d44494 p = 1) (hb : d271214 p = 1) : d350978 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d271214 q = 1) : d350975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d271214 q = 1) : d350976 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44493 q = 1) (hb : d271214 q = 1) : d350977 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, d350977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, d350977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44494 q = 1) (hb : d271214 q = 1) : d350978 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44494, d350978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44494, d350978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101023 (p : Pattern) (ha : d44498 p = 1) (hb : d271214 p = 1) : d350982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d271214 q = 1) : d350979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d271214 q = 1) : d350980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44497 q = 1) (hb : d271214 q = 1) : d350981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, d350981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, d350981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44498 q = 1) (hb : d271214 q = 1) : d350982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44498, d350982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44498, d350982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101024 (p : Pattern) (ha : d44504 p = 1) (hb : d271214 p = 1) : d350988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d271214 q = 1) : d350983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101022 q ha hb
    | true =>
      simp only [d44499, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101023 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d271214 q = 1) : d350984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d271214 q = 1) : d350985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d271214 q = 1) : d350986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d271214 q = 1) : d350987 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44504 q = 1) (hb : d271214 q = 1) : d350988 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, d350988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44504, d350988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101025 (p : Pattern) (ha : d44507 p = 1) (hb : d271214 p = 1) : d350991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d271214 q = 1) : d350975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d271214 q = 1) : d350976 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44493 q = 1) (hb : d271214 q = 1) : d350977 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, d350977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44493, d350977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44507 q = 1) (hb : d271214 q = 1) : d350991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44507, d350991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44507, d350991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101026 (p : Pattern) (ha : d44508 p = 1) (hb : d271214 p = 1) : d350992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d271214 q = 1) : d350979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d271214 q = 1) : d350980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44497 q = 1) (hb : d271214 q = 1) : d350981 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, d350981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44497, d350981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44508 q = 1) (hb : d271214 q = 1) : d350992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44508, d350992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44508, d350992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101027 (p : Pattern) (ha : d44514 p = 1) (hb : d271214 p = 1) : d350998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d271214 q = 1) : d350983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101022 q ha hb
    | true =>
      simp only [d44499, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101023 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d271214 q = 1) : d350984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d271214 q = 1) : d350985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d271214 q = 1) : d350986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d271214 q = 1) : d350987 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44509 q = 1) (hb : d271214 q = 1) : d350993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, d350993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101025 q ha hb
    | true =>
      simp only [d44509, d350993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101026 q ha hb
  have h7 (q : Pattern) (ha : d44510 q = 1) (hb : d271214 q = 1) : d350994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44510, d350994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44511 q = 1) (hb : d271214 q = 1) : d350995 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44511, d350995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44512 q = 1) (hb : d271214 q = 1) : d350996 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44512, d350996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44513 q = 1) (hb : d271214 q = 1) : d350997 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44513, d350997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44514 q = 1) (hb : d271214 q = 1) : d350998 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, d350998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44514, d350998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101028 (p : Pattern) (ha : d44665 p = 1) (hb : d271214 p = 1) : d351079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44499 q = 1) (hb : d271214 q = 1) : d350983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101022 q ha hb
    | true =>
      simp only [d44499, d350983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101023 q ha hb
  have h2 (q : Pattern) (ha : d44500 q = 1) (hb : d271214 q = 1) : d350984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44500, d350984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44501 q = 1) (hb : d271214 q = 1) : d350985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44501, d350985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44502 q = 1) (hb : d271214 q = 1) : d350986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44502, d350986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44503 q = 1) (hb : d271214 q = 1) : d350987 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44503, d350987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44660 q = 1) (hb : d271214 q = 1) : d351074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, d351074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101023 q ha hb
    | true =>
      simp only [d44660, d351074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44661 q = 1) (hb : d271214 q = 1) : d351075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, d351075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44661, d351075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44662 q = 1) (hb : d271214 q = 1) : d351076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, d351076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44662, d351076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44663 q = 1) (hb : d271214 q = 1) : d351077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, d351077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44663, d351077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44664 q = 1) (hb : d271214 q = 1) : d351078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, d351078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44664, d351078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44665 q = 1) (hb : d271214 q = 1) : d351079 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44665, d351079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44665, d351079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101029 (p : Pattern) (ha : d44671 p = 1) (hb : d271214 p = 1) : d351085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44660 q = 1) (hb : d271214 q = 1) : d351074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, d351074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101023 q ha hb
    | true =>
      simp only [d44660, d351074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44661 q = 1) (hb : d271214 q = 1) : d351075 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, d351075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44661, d351075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44662 q = 1) (hb : d271214 q = 1) : d351076 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, d351076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44662, d351076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44663 q = 1) (hb : d271214 q = 1) : d351077 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, d351077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44663, d351077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44664 q = 1) (hb : d271214 q = 1) : d351078 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, d351078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44664, d351078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44666 q = 1) (hb : d271214 q = 1) : d351080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, d351080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101026 q ha hb
    | true =>
      simp only [d44666, d351080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44667 q = 1) (hb : d271214 q = 1) : d351081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, d351081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44667, d351081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44668 q = 1) (hb : d271214 q = 1) : d351082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, d351082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44668, d351082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44669 q = 1) (hb : d271214 q = 1) : d351083 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, d351083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44669, d351083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44670 q = 1) (hb : d271214 q = 1) : d351084 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, d351084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44670, d351084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44671 q = 1) (hb : d271214 q = 1) : d351085 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44671, d351085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44671, d351085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101030 (p : Pattern) (ha : d44680 p = 1) (hb : d271214 p = 1) : d351094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44666 q = 1) (hb : d271214 q = 1) : d351080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, d351080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101026 q ha hb
    | true =>
      simp only [d44666, d351080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44667 q = 1) (hb : d271214 q = 1) : d351081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, d351081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44667, d351081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44668 q = 1) (hb : d271214 q = 1) : d351082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, d351082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44668, d351082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44669 q = 1) (hb : d271214 q = 1) : d351083 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, d351083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44669, d351083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44670 q = 1) (hb : d271214 q = 1) : d351084 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, d351084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44670, d351084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44680 q = 1) (hb : d271214 q = 1) : d351094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44680, d351094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44680, d351094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101031 (p : Pattern) (ha : d44702 p = 1) (hb : d271214 p = 1) : d351110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44692 q = 1) (hb : d271214 q = 1) : d351100 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
  have h8 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44693 q = 1) (hb : d271214 q = 1) : d351101 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44694 q = 1) (hb : d271214 q = 1) : d351102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44695 q = 1) (hb : d271214 q = 1) : d351103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44696 q = 1) (hb : d271214 q = 1) : d351104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d351104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d351104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44701 q = 1) (hb : d271214 q = 1) : d351109 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d351109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44701, d351109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44702 q = 1) (hb : d271214 q = 1) : d351110 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44702, d351110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44702, d351110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101032 (p : Pattern) (ha : d44712 p = 1) (hb : d271214 p = 1) : d351115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44692 q = 1) (hb : d271214 q = 1) : d351100 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
  have h2 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44693 q = 1) (hb : d271214 q = 1) : d351101 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44694 q = 1) (hb : d271214 q = 1) : d351102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44695 q = 1) (hb : d271214 q = 1) : d351103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44701 q = 1) (hb : d271214 q = 1) : d351109 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, d351109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44701, d351109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44711 q = 1) (hb : d271214 q = 1) : d44711 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d44712 q = 1) (hb : d271214 q = 1) : d351115 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44712, d351115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44712, d351115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro101033 (p : Pattern) (ha : d44731 p = 1) (hb : d271214 p = 1) : d351134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44713 q = 1) (hb : d271214 q = 1) : d351116 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101031 q ha hb
    | true =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101032 q ha hb
  have h2 (q : Pattern) (ha : d44714 q = 1) (hb : d271214 q = 1) : d351117 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44715 q = 1) (hb : d271214 q = 1) : d351118 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44721 q = 1) (hb : d271214 q = 1) : d351124 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d351124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44721, d351124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44730 q = 1) (hb : d271214 q = 1) : d351133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44730, d351133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44730, d351133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44731 q = 1) (hb : d271214 q = 1) : d351134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44731, d351134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44731, d351134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101034 (p : Pattern) (ha : d44813 p = 1) (hb : d271214 p = 1) : d351166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44732 q = 1) (hb : d271214 q = 1) : d351135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d351135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101033 q ha hb
    | true =>
      simp only [d44732, d351135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44733 q = 1) (hb : d271214 q = 1) : d351136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d351136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d351136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44810 q = 1) (hb : d271214 q = 1) : d351163 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44810, d351163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44810, d351163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44811 q = 1) (hb : d271214 q = 1) : d351164 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44811, d351164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44811, d351164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44812 q = 1) (hb : d271214 q = 1) : d351165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44812, d351165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44812, d351165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44813 q = 1) (hb : d271214 q = 1) : d351166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44813, d351166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44813, d351166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101035 (p : Pattern) (ha : d44819 p = 1) (hb : d271214 p = 1) : d351172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44814 q = 1) (hb : d271214 q = 1) : d351167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44814, d351167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101034 q ha hb
    | true =>
      simp only [d44814, d351167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44815 q = 1) (hb : d271214 q = 1) : d351168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44815, d351168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44815, d351168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44816 q = 1) (hb : d271214 q = 1) : d351169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44816, d351169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44816, d351169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44817 q = 1) (hb : d271214 q = 1) : d351170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44817, d351170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44817, d351170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44818 q = 1) (hb : d271214 q = 1) : d351171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44818, d351171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44818, d351171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44819 q = 1) (hb : d271214 q = 1) : d351172 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44819, d351172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44819, d351172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101036 (p : Pattern) (ha : d44519 p = 1) (hb : d271214 p = 1) : d351003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d271214 q = 1) : d350975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d271214 q = 1) : d350976 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44518 q = 1) (hb : d271214 q = 1) : d351002 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, d351002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44518, d351002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44519 q = 1) (hb : d271214 q = 1) : d351003 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44519, d351003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44519, d351003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101037 (p : Pattern) (ha : d44521 p = 1) (hb : d271214 p = 1) : d351005 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d271214 q = 1) : d350979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d271214 q = 1) : d350980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44520 q = 1) (hb : d271214 q = 1) : d351004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, d351004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44520, d351004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44521 q = 1) (hb : d271214 q = 1) : d351005 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44521, d351005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44521, d351005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101038 (p : Pattern) (ha : d44528 p = 1) (hb : d271214 p = 1) : d351012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d271214 q = 1) : d350975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44526 q = 1) (hb : d271214 q = 1) : d351010 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, d351010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44526, d351010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44527 q = 1) (hb : d271214 q = 1) : d351011 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, d351011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, d351011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44528 q = 1) (hb : d271214 q = 1) : d351012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44528, d351012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44528, d351012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101039 (p : Pattern) (ha : d44531 p = 1) (hb : d271214 p = 1) : d351015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d271214 q = 1) : d350979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44529 q = 1) (hb : d271214 q = 1) : d351013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, d351013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44529, d351013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44530 q = 1) (hb : d271214 q = 1) : d351014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, d351014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, d351014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44531 q = 1) (hb : d271214 q = 1) : d351015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44531, d351015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44531, d351015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101040 (p : Pattern) (ha : d44535 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44449 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44535 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101041 (p : Pattern) (ha : d44541 p = 1) (hb : d271214 p = 1) : d351024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44536 q = 1) (hb : d271214 q = 1) : d351019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44536, d351019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101040 q ha hb
    | true =>
      simp only [d44536, d351019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101017 q ha hb
  have h2 (q : Pattern) (ha : d44537 q = 1) (hb : d271214 q = 1) : d351020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44537, d351020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44537, d351020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44538 q = 1) (hb : d271214 q = 1) : d351021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44538, d351021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44538, d351021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44468 q = 1) (hb : d271214 q = 1) : d350958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d350958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101017 q ha hb
    | true =>
      simp only [d44468, d350958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101018 q ha hb
  have h5 (q : Pattern) (ha : d44469 q = 1) (hb : d271214 q = 1) : d350959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d350959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d350959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44470 q = 1) (hb : d271214 q = 1) : d350960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d350960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d350960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44539 q = 1) (hb : d271214 q = 1) : d351022 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44539, d351022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44539, d351022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44478 q = 1) (hb : d271214 q = 1) : d350962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101018 q ha hb
    | true =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101019 q ha hb
  have h9 (q : Pattern) (ha : d44479 q = 1) (hb : d271214 q = 1) : d350963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44480 q = 1) (hb : d271214 q = 1) : d350964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44481 q = 1) (hb : d271214 q = 1) : d350965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d350965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44481, d350965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44540 q = 1) (hb : d271214 q = 1) : d351023 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44540, d351023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44540, d351023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44541 q = 1) (hb : d271214 q = 1) : d351024 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44541, d351024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44541, d351024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro101042 (p : Pattern) (ha : d44547 p = 1) (hb : d271214 p = 1) : d351030 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44542 q = 1) (hb : d271214 q = 1) : d351025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, d351025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101041 q ha hb
    | true =>
      simp only [d44542, d351025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44543 q = 1) (hb : d271214 q = 1) : d351026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, d351026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44543, d351026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44544 q = 1) (hb : d271214 q = 1) : d351027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, d351027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, d351027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44545 q = 1) (hb : d271214 q = 1) : d351028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, d351028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, d351028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44546 q = 1) (hb : d271214 q = 1) : d351029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, d351029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, d351029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44547 q = 1) (hb : d271214 q = 1) : d351030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44547, d351030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44547, d351030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101043 (p : Pattern) (ha : d44609 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d35372 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101014 q ha hb
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101013 q ha hb
  have h3 (q : Pattern) (ha : d35373 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44441 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44442 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44443 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44609 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro101044 (p : Pattern) (ha : d44615 p = 1) (hb : d271214 p = 1) : d351033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44447 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44448 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44462 q = 1) (hb : d271214 q = 1) : d350952 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44462, d350952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44463 q = 1) (hb : d271214 q = 1) : d350953 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44463, d350953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44464 q = 1) (hb : d271214 q = 1) : d350954 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, d350954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44464, d350954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44610 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101043 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44611 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44612 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44613 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44614 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d44615 q = 1) (hb : d271214 q = 1) : d351033 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44615, d351033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44615, d351033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101045 (p : Pattern) (ha : d44616 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44610 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101043 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44611 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44612 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44613 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44614 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44616 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101046 (p : Pattern) (ha : d44622 p = 1) (hb : d271214 p = 1) : d351039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44468 q = 1) (hb : d271214 q = 1) : d350958 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, d350958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101017 q ha hb
    | true =>
      simp only [d44468, d350958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101018 q ha hb
  have h2 (q : Pattern) (ha : d44469 q = 1) (hb : d271214 q = 1) : d350959 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, d350959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44469, d350959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44470 q = 1) (hb : d271214 q = 1) : d350960 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, d350960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44470, d350960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44478 q = 1) (hb : d271214 q = 1) : d350962 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101018 q ha hb
    | true =>
      simp only [d44478, d350962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101019 q ha hb
  have h5 (q : Pattern) (ha : d44479 q = 1) (hb : d271214 q = 1) : d350963 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44479, d350963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44480 q = 1) (hb : d271214 q = 1) : d350964 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44480, d350964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44481 q = 1) (hb : d271214 q = 1) : d350965 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, d350965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44481, d350965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44617 q = 1) (hb : d271214 q = 1) : d351034 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44617, d351034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101044 q ha hb
    | true =>
      simp only [d44617, d351034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101045 q ha hb
  have h9 (q : Pattern) (ha : d44618 q = 1) (hb : d271214 q = 1) : d351035 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44618, d351035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44618, d351035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44619 q = 1) (hb : d271214 q = 1) : d351036 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44619, d351036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44619, d351036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44620 q = 1) (hb : d271214 q = 1) : d351037 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44620, d351037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44620, d351037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44621 q = 1) (hb : d271214 q = 1) : d351038 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44621, d351038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44621, d351038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44622 q = 1) (hb : d271214 q = 1) : d351039 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44622, d351039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44622, d351039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro101047 (p : Pattern) (ha : d44628 p = 1) (hb : d271214 p = 1) : d351045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44623 q = 1) (hb : d271214 q = 1) : d351040 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, d351040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101046 q ha hb
    | true =>
      simp only [d44623, d351040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44624 q = 1) (hb : d271214 q = 1) : d351041 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, d351041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44624, d351041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44625 q = 1) (hb : d271214 q = 1) : d351042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, d351042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, d351042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44626 q = 1) (hb : d271214 q = 1) : d351043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, d351043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, d351043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44627 q = 1) (hb : d271214 q = 1) : d351044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, d351044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, d351044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44628 q = 1) (hb : d271214 q = 1) : d351045 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44628, d351045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44628, d351045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101048 (p : Pattern) (ha : d271214 p = 1) (hb : d309471 p = 1) : d351051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44522 q = 1) (hb : d271214 q = 1) : d351006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, d351006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101036 q ha hb
    | true =>
      simp only [d44522, d351006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101037 q ha hb
  have h2 (q : Pattern) (ha : d44523 q = 1) (hb : d271214 q = 1) : d351007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, d351007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44523, d351007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44524 q = 1) (hb : d271214 q = 1) : d351008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, d351008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, d351008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44525 q = 1) (hb : d271214 q = 1) : d351009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, d351009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44525, d351009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44532 q = 1) (hb : d271214 q = 1) : d351016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, d351016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101038 q ha hb
    | true =>
      simp only [d44532, d351016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101039 q ha hb
  have h6 (q : Pattern) (ha : d44533 q = 1) (hb : d271214 q = 1) : d351017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, d351017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44533, d351017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44534 q = 1) (hb : d271214 q = 1) : d351018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, d351018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, d351018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44548 q = 1) (hb : d271214 q = 1) : d351031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, d351031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101042 q ha hb
    | true =>
      simp only [d44548, d351031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101022 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309467 q = 1) : d351032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d351032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d309467, d351032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d44629 q = 1) (hb : d271214 q = 1) : d351046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, d351046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101047 q ha hb
    | true =>
      simp only [d44629, d351046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44630 q = 1) (hb : d271214 q = 1) : d351047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, d351047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44630, d351047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309468 q = 1) : d351048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d351048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309468, d351048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309469 q = 1) : d351049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d351049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309469, d351049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309470 q = 1) : d351050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d351050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309470, d351050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309471 q = 1) : d351051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309471, d351051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309471, d351051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101049 (p : Pattern) (ha : d44635 p = 1) (hb : d271214 p = 1) : d351052 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d271214 q = 1) : d350975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44492 q = 1) (hb : d271214 q = 1) : d350976 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44492, d350976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44518 q = 1) (hb : d271214 q = 1) : d351002 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, d351002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44518, d351002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44635 q = 1) (hb : d271214 q = 1) : d351052 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44635, d351052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44635, d351052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101050 (p : Pattern) (ha : d44636 p = 1) (hb : d271214 p = 1) : d351053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d271214 q = 1) : d350979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44496 q = 1) (hb : d271214 q = 1) : d350980 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44496, d350980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44520 q = 1) (hb : d271214 q = 1) : d351004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, d351004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44520, d351004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44636 q = 1) (hb : d271214 q = 1) : d351053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44636, d351053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44636, d351053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101051 (p : Pattern) (ha : d44641 p = 1) (hb : d271214 p = 1) : d351058 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44491 q = 1) (hb : d271214 q = 1) : d350975 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44491, d350975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44526 q = 1) (hb : d271214 q = 1) : d351010 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, d351010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44526, d351010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44527 q = 1) (hb : d271214 q = 1) : d351011 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, d351011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44527, d351011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44641 q = 1) (hb : d271214 q = 1) : d351058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44641, d351058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44641, d351058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101052 (p : Pattern) (ha : d44642 p = 1) (hb : d271214 p = 1) : d351059 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44489 q = 1) (hb : d271214 q = 1) : d350973 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101021 q ha hb
    | true =>
      simp only [d44489, d350973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44490 q = 1) (hb : d271214 q = 1) : d350974 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44490, d350974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44495 q = 1) (hb : d271214 q = 1) : d350979 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44495, d350979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44529 q = 1) (hb : d271214 q = 1) : d351013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, d351013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44529, d351013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44530 q = 1) (hb : d271214 q = 1) : d351014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, d351014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44530, d351014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44642 q = 1) (hb : d271214 q = 1) : d351059 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44642, d351059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44642, d351059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101053 (p : Pattern) (ha : d44646 p = 1) (hb : d271214 p = 1) : d351063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44542 q = 1) (hb : d271214 q = 1) : d351025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, d351025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101041 q ha hb
    | true =>
      simp only [d44542, d351025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44543 q = 1) (hb : d271214 q = 1) : d351026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, d351026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44543, d351026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44485 q = 1) (hb : d271214 q = 1) : d350969 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101020 q ha hb
    | true =>
      simp only [d44485, d350969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44486 q = 1) (hb : d271214 q = 1) : d350970 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44486, d350970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44544 q = 1) (hb : d271214 q = 1) : d351027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, d351027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44544, d351027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44545 q = 1) (hb : d271214 q = 1) : d351028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, d351028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44545, d351028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44546 q = 1) (hb : d271214 q = 1) : d351029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, d351029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44546, d351029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44646 q = 1) (hb : d271214 q = 1) : d351063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44646, d351063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44646, d351063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101054 (p : Pattern) (ha : d44652 p = 1) (hb : d271214 p = 1) : d351066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44623 q = 1) (hb : d271214 q = 1) : d351040 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, d351040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101046 q ha hb
    | true =>
      simp only [d44623, d351040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44624 q = 1) (hb : d271214 q = 1) : d351041 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, d351041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44624, d351041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44625 q = 1) (hb : d271214 q = 1) : d351042 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, d351042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44625, d351042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44626 q = 1) (hb : d271214 q = 1) : d351043 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, d351043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44626, d351043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44627 q = 1) (hb : d271214 q = 1) : d351044 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, d351044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44627, d351044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44652 q = 1) (hb : d271214 q = 1) : d351066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44652, d351066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44652, d351066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101055 (p : Pattern) (ha : d271214 p = 1) (hb : d309476 p = 1) : d351072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44522 q = 1) (hb : d271214 q = 1) : d351006 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, d351006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101036 q ha hb
    | true =>
      simp only [d44522, d351006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101037 q ha hb
  have h2 (q : Pattern) (ha : d44523 q = 1) (hb : d271214 q = 1) : d351007 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, d351007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44523, d351007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44524 q = 1) (hb : d271214 q = 1) : d351008 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, d351008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44524, d351008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44525 q = 1) (hb : d271214 q = 1) : d351009 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, d351009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44525, d351009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44532 q = 1) (hb : d271214 q = 1) : d351016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, d351016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101038 q ha hb
    | true =>
      simp only [d44532, d351016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101039 q ha hb
  have h6 (q : Pattern) (ha : d44533 q = 1) (hb : d271214 q = 1) : d351017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, d351017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44533, d351017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44534 q = 1) (hb : d271214 q = 1) : d351018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, d351018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44534, d351018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44548 q = 1) (hb : d271214 q = 1) : d351031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, d351031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101042 q ha hb
    | true =>
      simp only [d44548, d351031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101022 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309467 q = 1) : d351032 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309467, d351032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d309467, d351032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d44629 q = 1) (hb : d271214 q = 1) : d351046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, d351046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101047 q ha hb
    | true =>
      simp only [d44629, d351046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44630 q = 1) (hb : d271214 q = 1) : d351047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, d351047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44630, d351047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309468 q = 1) : d351048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309468, d351048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309468, d351048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309469 q = 1) : d351049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309469, d351049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309469, d351049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309470 q = 1) : d351050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309470, d351050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309470, d351050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d44637 q = 1) (hb : d271214 q = 1) : d351054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44637, d351054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101049 q ha hb
    | true =>
      simp only [d44637, d351054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101050 q ha hb
  have h16 (q : Pattern) (ha : d44638 q = 1) (hb : d271214 q = 1) : d351055 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44638, d351055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44638, d351055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44639 q = 1) (hb : d271214 q = 1) : d351056 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44639, d351056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44639, d351056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d44640 q = 1) (hb : d271214 q = 1) : d351057 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44640, d351057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44640, d351057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d44643 q = 1) (hb : d271214 q = 1) : d351060 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44643, d351060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101051 q ha hb
    | true =>
      simp only [d44643, d351060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101052 q ha hb
  have h20 (q : Pattern) (ha : d44644 q = 1) (hb : d271214 q = 1) : d351061 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44644, d351061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44644, d351061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d44645 q = 1) (hb : d271214 q = 1) : d351062 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44645, d351062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d44645, d351062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d44647 q = 1) (hb : d271214 q = 1) : d351064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, d351064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101053 q ha hb
    | true =>
      simp only [d44647, d351064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101025 q ha hb
  have h23 (q : Pattern) (ha : d271214 q = 1) (hb : d309472 q = 1) : d351065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d351065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d309472, d351065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d44653 q = 1) (hb : d271214 q = 1) : d351067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, d351067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101054 q ha hb
    | true =>
      simp only [d44653, d351067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d44654 q = 1) (hb : d271214 q = 1) : d351068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, d351068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d44654, d351068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d271214 q = 1) (hb : d309473 q = 1) : d351069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d351069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309473, d351069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d271214 q = 1) (hb : d309474 q = 1) : d351070 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309474, d351070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d309474, d351070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d271214 q = 1) (hb : d309475 q = 1) : d351071 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309475, d351071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d309475, d351071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d271214 q = 1) (hb : d309476 q = 1) : d351072 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309476, d351072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309476, d351072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro101056 (p : Pattern) (ha : d271214 p = 1) (hb : d309483 p = 1) : d351092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44647 q = 1) (hb : d271214 q = 1) : d351064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, d351064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101053 q ha hb
    | true =>
      simp only [d44647, d351064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101025 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309472 q = 1) : d351065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309472, d351065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309472, d351065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d44653 q = 1) (hb : d271214 q = 1) : d351067 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, d351067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101054 q ha hb
    | true =>
      simp only [d44653, d351067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44654 q = 1) (hb : d271214 q = 1) : d351068 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, d351068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44654, d351068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309473 q = 1) : d351069 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309473, d351069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309473, d351069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309481 q = 1) : d351090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309481, d351090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309481, d351090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309482 q = 1) : d351091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309482, d351091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309482, d351091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309483 q = 1) : d351092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309483, d351092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309483, d351092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101057 (p : Pattern) (ha : d44691 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44690 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44691 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101058 (p : Pattern) (ha : d44697 p = 1) (hb : d271214 p = 1) : d351105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44690 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44692 q = 1) (hb : d271214 q = 1) : d351100 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
  have h9 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d44693 q = 1) (hb : d271214 q = 1) : d351101 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44694 q = 1) (hb : d271214 q = 1) : d351102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44695 q = 1) (hb : d271214 q = 1) : d351103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d44696 q = 1) (hb : d271214 q = 1) : d351104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d351104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d351104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d44697 q = 1) (hb : d271214 q = 1) : d351105 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44697, d351105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44697, d351105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101059 (p : Pattern) (ha : d44718 p = 1) (hb : d271214 p = 1) : d351121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44698 q = 1) (hb : d271214 q = 1) : d351106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44698, d351106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101057 q ha hb
    | true =>
      simp only [d44698, d351106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101058 q ha hb
  have h2 (q : Pattern) (ha : d44699 q = 1) (hb : d271214 q = 1) : d351107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44699, d351107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44699, d351107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44700 q = 1) (hb : d271214 q = 1) : d351108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44700, d351108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44700, d351108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44703 q = 1) (hb : d271214 q = 1) : d351111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d351111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101058 q ha hb
    | true =>
      simp only [d44703, d351111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101031 q ha hb
  have h5 (q : Pattern) (ha : d44704 q = 1) (hb : d271214 q = 1) : d351112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d351112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d351112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44705 q = 1) (hb : d271214 q = 1) : d351113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d351113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d351113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44706 q = 1) (hb : d271214 q = 1) : d351114 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44706, d351114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44706, d351114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44713 q = 1) (hb : d271214 q = 1) : d351116 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101031 q ha hb
    | true =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101032 q ha hb
  have h9 (q : Pattern) (ha : d44714 q = 1) (hb : d271214 q = 1) : d351117 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44715 q = 1) (hb : d271214 q = 1) : d351118 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44716 q = 1) (hb : d271214 q = 1) : d351119 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d351119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44716, d351119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44717 q = 1) (hb : d271214 q = 1) : d351120 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44717, d351120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44717, d351120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44718 q = 1) (hb : d271214 q = 1) : d351121 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44718, d351121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44718, d351121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro101060 (p : Pattern) (ha : d44723 p = 1) (hb : d271214 p = 1) : d351126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44703 q = 1) (hb : d271214 q = 1) : d351111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d351111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101058 q ha hb
    | true =>
      simp only [d44703, d351111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101031 q ha hb
  have h2 (q : Pattern) (ha : d44704 q = 1) (hb : d271214 q = 1) : d351112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d351112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d351112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44705 q = 1) (hb : d271214 q = 1) : d351113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d351113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d351113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44713 q = 1) (hb : d271214 q = 1) : d351116 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101031 q ha hb
    | true =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101032 q ha hb
  have h5 (q : Pattern) (ha : d44714 q = 1) (hb : d271214 q = 1) : d351117 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44715 q = 1) (hb : d271214 q = 1) : d351118 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44716 q = 1) (hb : d271214 q = 1) : d351119 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d351119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, d351119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44721 q = 1) (hb : d271214 q = 1) : d351124 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, d351124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44721, d351124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44722 q = 1) (hb : d271214 q = 1) : d351125 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44722, d351125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44722, d351125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44723 q = 1) (hb : d271214 q = 1) : d351126 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44723, d351126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44723, d351126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro101061 (p : Pattern) (ha : d44729 p = 1) (hb : d271214 p = 1) : d351132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44719 q = 1) (hb : d271214 q = 1) : d351122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44719, d351122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101059 q ha hb
    | true =>
      simp only [d44719, d351122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44720 q = 1) (hb : d271214 q = 1) : d351123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44720, d351123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44720, d351123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44724 q = 1) (hb : d271214 q = 1) : d351127 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, d351127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101060 q ha hb
    | true =>
      simp only [d44724, d351127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44725 q = 1) (hb : d271214 q = 1) : d351128 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, d351128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44725, d351128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44726 q = 1) (hb : d271214 q = 1) : d351129 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44726, d351129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44726, d351129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44727 q = 1) (hb : d271214 q = 1) : d351130 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44727, d351130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44727, d351130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44728 q = 1) (hb : d271214 q = 1) : d351131 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44728, d351131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44728, d351131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44729 q = 1) (hb : d271214 q = 1) : d351132 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44729, d351132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44729, d351132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101062 (p : Pattern) (ha : d44737 p = 1) (hb : d271214 p = 1) : d351140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44724 q = 1) (hb : d271214 q = 1) : d351127 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, d351127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101060 q ha hb
    | true =>
      simp only [d44724, d351127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44725 q = 1) (hb : d271214 q = 1) : d351128 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, d351128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44725, d351128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44732 q = 1) (hb : d271214 q = 1) : d351135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, d351135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101033 q ha hb
    | true =>
      simp only [d44732, d351135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44733 q = 1) (hb : d271214 q = 1) : d351136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, d351136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44733, d351136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d44734 q = 1) (hb : d271214 q = 1) : d351137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44734, d351137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44734, d351137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44735 q = 1) (hb : d271214 q = 1) : d351138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44735, d351138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44735, d351138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44736 q = 1) (hb : d271214 q = 1) : d351139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44736, d351139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44736, d351139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44737 q = 1) (hb : d271214 q = 1) : d351140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44737, d351140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44737, d351140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101063 (p : Pattern) (ha : d44789 p = 1) (hb : d271214 p = 1) : d351143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44686 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
  have h2 (q : Pattern) (ha : d44445 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101015 q ha hb
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44687 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44446 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44688 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44689 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44692 q = 1) (hb : d271214 q = 1) : d351100 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44692, d351100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
  have h8 (q : Pattern) (ha : d44460 q = 1) (hb : d271214 q = 1) : d350950 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101016 q ha hb
    | true =>
      simp only [d44460, d350950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d44693 q = 1) (hb : d271214 q = 1) : d351101 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44693, d351101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44461 q = 1) (hb : d271214 q = 1) : d350951 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d44461, d350951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44694 q = 1) (hb : d271214 q = 1) : d351102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d44694, d351102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d44695 q = 1) (hb : d271214 q = 1) : d351103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d44695, d351103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d44696 q = 1) (hb : d271214 q = 1) : d351104 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, d351104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44696, d351104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d44784 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101043 q ha hb
  have h15 (q : Pattern) (ha : d44610 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101043 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d44785 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d44611 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d44786 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d44787 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d44788 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d44789 q = 1) (hb : d271214 q = 1) : d351143 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44789, d351143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d44789, d351143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro101064 (p : Pattern) (ha : d44790 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44784 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101043 q ha hb
  have h2 (q : Pattern) (ha : d44610 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101043 q ha hb
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44785 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44611 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44786 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44787 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44788 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d44790 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101065 (p : Pattern) (ha : d44796 p = 1) (hb : d271214 p = 1) : d351149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44703 q = 1) (hb : d271214 q = 1) : d351111 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, d351111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101058 q ha hb
    | true =>
      simp only [d44703, d351111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101031 q ha hb
  have h2 (q : Pattern) (ha : d44704 q = 1) (hb : d271214 q = 1) : d351112 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, d351112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44704, d351112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44705 q = 1) (hb : d271214 q = 1) : d351113 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, d351113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44705, d351113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d44713 q = 1) (hb : d271214 q = 1) : d351116 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101031 q ha hb
    | true =>
      simp only [d44713, d351116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101032 q ha hb
  have h5 (q : Pattern) (ha : d44714 q = 1) (hb : d271214 q = 1) : d351117 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44714, d351117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44715 q = 1) (hb : d271214 q = 1) : d351118 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44715, d351118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44716 q = 1) (hb : d271214 q = 1) : d351119 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, d351119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44716, d351119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d44791 q = 1) (hb : d271214 q = 1) : d351144 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44791, d351144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101063 q ha hb
    | true =>
      simp only [d44791, d351144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101064 q ha hb
  have h9 (q : Pattern) (ha : d44792 q = 1) (hb : d271214 q = 1) : d351145 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44792, d351145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44792, d351145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d44793 q = 1) (hb : d271214 q = 1) : d351146 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44793, d351146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44793, d351146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d44794 q = 1) (hb : d271214 q = 1) : d351147 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44794, d351147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44794, d351147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d44795 q = 1) (hb : d271214 q = 1) : d351148 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44795, d351148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d44795, d351148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d44796 q = 1) (hb : d271214 q = 1) : d351149 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44796, d351149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44796, d351149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro101066 (p : Pattern) (ha : d44802 p = 1) (hb : d271214 p = 1) : d351155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44797 q = 1) (hb : d271214 q = 1) : d351150 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44797, d351150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101065 q ha hb
    | true =>
      simp only [d44797, d351150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d44798 q = 1) (hb : d271214 q = 1) : d351151 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44798, d351151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44798, d351151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d44799 q = 1) (hb : d271214 q = 1) : d351152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44799, d351152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44799, d351152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44800 q = 1) (hb : d271214 q = 1) : d351153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44800, d351153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44800, d351153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44801 q = 1) (hb : d271214 q = 1) : d351154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44801, d351154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d44801, d351154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44802 q = 1) (hb : d271214 q = 1) : d351155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44802, d351155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d44802, d351155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101067 (p : Pattern) (ha : d271214 p = 1) (hb : d309493 p = 1) : d351161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44738 q = 1) (hb : d271214 q = 1) : d351141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44738, d351141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101061 q ha hb
    | true =>
      simp only [d44738, d351141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101062 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309489 q = 1) : d351142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309489, d351142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309489, d351142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d44803 q = 1) (hb : d271214 q = 1) : d351156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44803, d351156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101066 q ha hb
    | true =>
      simp only [d44803, d351156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d44804 q = 1) (hb : d271214 q = 1) : d351157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44804, d351157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44804, d351157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309490 q = 1) : d351158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309490, d351158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309490, d351158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309491 q = 1) : d351159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309491, d351159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309491, d351159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309492 q = 1) : d351160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309492, d351160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309492, d351160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309493 q = 1) : d351161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309493, d351161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309493, d351161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101068 (p : Pattern) (ha : d271214 p = 1) (hb : d309499 p = 1) : d351178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d44505 q = 1) (hb : d271214 q = 1) : d350989 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44505, d350989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44505, d350989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101024 q ha hb
  have h2 (q : Pattern) (ha : d44506 q = 1) (hb : d271214 q = 1) : d350990 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44506, d350990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d44506, d350990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d44515 q = 1) (hb : d271214 q = 1) : d350999 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, d350999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101024 q ha hb
    | true =>
      simp only [d44515, d350999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101027 q ha hb
  have h4 (q : Pattern) (ha : d44516 q = 1) (hb : d271214 q = 1) : d351000 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, d351000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d44516, d351000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d44517 q = 1) (hb : d271214 q = 1) : d351001 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44517, d351001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d44517, d351001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309477 q = 1) : d351073 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309477, d351073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101048 q ha hb
    | true =>
      simp only [d309477, d351073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101055 q ha hb
  have h7 (q : Pattern) (ha : d44672 q = 1) (hb : d271214 q = 1) : d351086 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44672, d351086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101028 q ha hb
    | true =>
      simp only [d44672, d351086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101029 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309478 q = 1) : d351087 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309478, d351087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309478, d351087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309479 q = 1) : d351088 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309479, d351088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309479, d351088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d271214 q = 1) (hb : d309480 q = 1) : d351089 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309480, d351089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d309480, d351089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309484 q = 1) : d351093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309484, d351093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309484, d351093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101056 q ha hb
  have h12 (q : Pattern) (ha : d44681 q = 1) (hb : d271214 q = 1) : d351095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44681, d351095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44681, d351095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101030 q ha hb
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309485 q = 1) : d351096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309485, d351096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309485, d351096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309486 q = 1) : d351097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309486, d351097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309486, d351097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309487 q = 1) : d351098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309487, d351098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309487, d351098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309488 q = 1) : d351099 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309488, d351099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309488, d351099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271214 q = 1) (hb : d309494 q = 1) : d351162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309494, d351162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309494, d351162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101067 q ha hb
  have h18 (q : Pattern) (ha : d44820 q = 1) (hb : d271214 q = 1) : d351173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44820, d351173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d44820, d351173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101035 q ha hb
  have h19 (q : Pattern) (ha : d271214 q = 1) (hb : d309495 q = 1) : d351174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309495, d351174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309495, d351174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d271214 q = 1) (hb : d309496 q = 1) : d351175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309496, d351175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309496, d351175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d271214 q = 1) (hb : d309497 q = 1) : d351176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309497, d351176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309497, d351176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d271214 q = 1) (hb : d309498 q = 1) : d351177 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309498, d351177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309498, d351177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d271214 q = 1) (hb : d309499 q = 1) : d351178 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309499, d351178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309499, d351178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro101069 (p : Pattern) (ha : d271214 p = 1) (hb : d309505 p = 1) : d351184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d309500 q = 1) : d351179 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309500, d351179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309500, d351179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101068 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309501 q = 1) : d351180 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309501, d351180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309501, d351180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d309502 q = 1) : d351181 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309502, d351181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309502, d351181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d309503 q = 1) : d351182 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309503, d351182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309503, d351182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309504 q = 1) : d351183 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309504, d351183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309504, d351183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309505 q = 1) : d351184 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309505, d351184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309505, d351184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101070 (p : Pattern) (ha : d42249 p = 1) (hb : d271214 p = 1) : d349491 p = 1 := by
  have h0 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42246 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d15 q = 1) (hb : d271214 q = 1) : d15 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42247 q = 1) (hb : d271214 q = 1) : d1540 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42247, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16 q = 1) (hb : d271214 q = 1) : d16 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42248 q = 1) (hb : d271214 q = 1) : d42960 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d42960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42248, d42960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17 q = 1) (hb : d271214 q = 1) : d17 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42249 q = 1) (hb : d271214 q = 1) : d349491 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42249, d349491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42249, d349491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101071 (p : Pattern) (ha : d42255 p = 1) (hb : d271214 p = 1) : d349497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d271214 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42253 q = 1) (hb : d271214 q = 1) : d349495 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d349495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42253, d349495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42254 q = 1) (hb : d271214 q = 1) : d349496 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d349496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42254, d349496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23 q = 1) (hb : d271214 q = 1) : d23 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d42255 q = 1) (hb : d271214 q = 1) : d349497 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42255, d349497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42255, d349497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro101072 (p : Pattern) (ha : d42261 p = 1) (hb : d271214 p = 1) : d349503 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42256 q = 1) (hb : d271214 q = 1) : d349498 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101071 q ha hb
    | true =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42257 q = 1) (hb : d271214 q = 1) : d349499 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42258 q = 1) (hb : d271214 q = 1) : d349500 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d349500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42258, d349500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42259 q = 1) (hb : d271214 q = 1) : d349501 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d349501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42259, d349501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d271214 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42260 q = 1) (hb : d271214 q = 1) : d349502 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42260, d349502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42260, d349502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d271214 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42261 q = 1) (hb : d271214 q = 1) : d349503 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42261, d349503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42261, d349503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101073 (p : Pattern) (ha : d42267 p = 1) (hb : d271214 p = 1) : d349509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d271214 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42262 q = 1) (hb : d271214 q = 1) : d349504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
    | true =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42263 q = 1) (hb : d271214 q = 1) : d349505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42264 q = 1) (hb : d271214 q = 1) : d349506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d271214 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42265 q = 1) (hb : d271214 q = 1) : d349507 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d349507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42265, d349507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d271214 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42266 q = 1) (hb : d271214 q = 1) : d349508 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42266, d349508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42266, d349508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42267 q = 1) (hb : d271214 q = 1) : d349509 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42267, d349509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42267, d349509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro101074 (p : Pattern) (ha : d42273 p = 1) (hb : d271214 p = 1) : d349515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d271214 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d271214 q = 1) : d349512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d271214 q = 1) : d349513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42272 q = 1) (hb : d271214 q = 1) : d349514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d349514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42272, d349514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42273 q = 1) (hb : d271214 q = 1) : d349515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42273, d349515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42273, d349515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101075 (p : Pattern) (ha : d271214 p = 1) (hb : d309771 p = 1) : d349521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d271214 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d271214 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d271214 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42274 q = 1) (hb : d271214 q = 1) : d349516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101074 q ha hb
    | true =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309767 q = 1) : d349517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d349517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309767, d349517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d271214 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309768 q = 1) : d349518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d349518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309768, d349518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309769 q = 1) : d349519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d349519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309769, d349519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309770 q = 1) : d349520 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d349520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309770, d349520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271214 q = 1) (hb : d309771 q = 1) : d349521 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309771, d349521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309771, d349521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro101076 (p : Pattern) (ha : d42280 p = 1) (hb : d271214 p = 1) : d349522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d271214 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d271214 q = 1) : d349512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d271214 q = 1) : d349513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42272 q = 1) (hb : d271214 q = 1) : d349514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42272, d349514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42272, d349514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42280 q = 1) (hb : d271214 q = 1) : d349522 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42280, d349522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42280, d349522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro101077 (p : Pattern) (ha : d271214 p = 1) (hb : d309776 p = 1) : d349528 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d271214 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d271214 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d271214 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42274 q = 1) (hb : d271214 q = 1) : d349516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101074 q ha hb
    | true =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309767 q = 1) : d349517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309767, d349517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d309767, d349517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d271214 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309768 q = 1) : d349518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309768, d349518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d309768, d349518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309769 q = 1) : d349519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309769, d349519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309769, d349519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309770 q = 1) : d349520 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309770, d349520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309770, d349520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d271214 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d271214 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d271214 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d42281 q = 1) (hb : d271214 q = 1) : d349523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101076 q ha hb
    | true =>
      simp only [d42281, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309772 q = 1) : d349524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d349524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d309772, d349524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d271214 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309773 q = 1) : d349525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d349525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309773, d349525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d271214 q = 1) (hb : d309774 q = 1) : d349526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309774, d349526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d309774, d349526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d271214 q = 1) (hb : d309775 q = 1) : d349527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309775, d349527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309775, d349527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d271214 q = 1) (hb : d309776 q = 1) : d349528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309776, d349528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309776, d349528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro101078 (p : Pattern) (ha : d271214 p = 1) (hb : d309783 p = 1) : d349535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d271214 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42281 q = 1) (hb : d271214 q = 1) : d349523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101076 q ha hb
    | true =>
      simp only [d42281, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d309772 q = 1) : d349524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309772, d349524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309772, d349524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d271214 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309773 q = 1) : d349525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309773, d349525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309773, d349525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309781 q = 1) : d349533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309781, d349533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309781, d349533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309782 q = 1) : d349534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309782, d349534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309782, d349534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309783 q = 1) : d349535 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309783, d349535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309783, d349535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101079 (p : Pattern) (ha : d42304 p = 1) (hb : d271214 p = 1) : d349546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42299 q = 1) (hb : d271214 q = 1) : d349541 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d349541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42299, d349541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101071 q ha hb
  have h2 (q : Pattern) (ha : d42256 q = 1) (hb : d271214 q = 1) : d349498 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101071 q ha hb
    | true =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42300 q = 1) (hb : d271214 q = 1) : d349542 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d349542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42300, d349542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42257 q = 1) (hb : d271214 q = 1) : d349499 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42301 q = 1) (hb : d271214 q = 1) : d349543 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d349543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42301, d349543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42302 q = 1) (hb : d271214 q = 1) : d349544 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d349544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42302, d349544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d271214 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42303 q = 1) (hb : d271214 q = 1) : d349545 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42303, d349545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42303, d349545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d271214 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42304 q = 1) (hb : d271214 q = 1) : d349546 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42304, d349546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42304, d349546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro101080 (p : Pattern) (ha : d42310 p = 1) (hb : d271214 p = 1) : d349552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d271214 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42305 q = 1) (hb : d271214 q = 1) : d349547 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
    | true =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42306 q = 1) (hb : d271214 q = 1) : d349548 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42307 q = 1) (hb : d271214 q = 1) : d349549 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d271214 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42308 q = 1) (hb : d271214 q = 1) : d349550 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d349550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42308, d349550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d271214 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42309 q = 1) (hb : d271214 q = 1) : d349551 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42309, d349551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42309, d349551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42310 q = 1) (hb : d271214 q = 1) : d349552 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42310, d349552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42310, d349552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro101081 (p : Pattern) (ha : d42316 p = 1) (hb : d271214 p = 1) : d349558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42311 q = 1) (hb : d271214 q = 1) : d349553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d349553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101080 q ha hb
    | true =>
      simp only [d42311, d349553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42312 q = 1) (hb : d271214 q = 1) : d349554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d349554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42312, d349554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d271214 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42313 q = 1) (hb : d271214 q = 1) : d349555 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42313, d349555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42313, d349555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42314 q = 1) (hb : d271214 q = 1) : d349556 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42314, d349556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42314, d349556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42315 q = 1) (hb : d271214 q = 1) : d349557 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42315, d349557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42315, d349557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42316 q = 1) (hb : d271214 q = 1) : d349558 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42316, d349558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42316, d349558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro101082 (p : Pattern) (ha : d271214 p = 1) (hb : d309793 p = 1) : d349564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d271214 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42317 q = 1) (hb : d271214 q = 1) : d349559 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42317, d349559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101081 q ha hb
    | true =>
      simp only [d42317, d349559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d309789 q = 1) : d349560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309789, d349560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d309789, d349560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d271214 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309790 q = 1) : d349561 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309790, d349561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309790, d349561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309791 q = 1) : d349562 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309791, d349562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309791, d349562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309792 q = 1) : d349563 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309792, d349563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309792, d349563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309793 q = 1) : d349564 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309793, d349564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309793, d349564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101083 (p : Pattern) (ha : d271214 p = 1) (hb : d309799 p = 1) : d349570 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d271214 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d309777 q = 1) : d349529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309777, d349529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101075 q ha hb
    | true =>
      simp only [d309777, d349529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101077 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d271214 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d309778 q = 1) : d349530 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309778, d349530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d309778, d349530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309779 q = 1) : d349531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309779, d349531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d309779, d349531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309780 q = 1) : d349532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309780, d349532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309780, d349532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309784 q = 1) : d349536 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309784, d349536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309784, d349536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101078 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309785 q = 1) : d349537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309785, d349537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d309785, d349537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309786 q = 1) : d349538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309786, d349538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309786, d349538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d271214 q = 1) (hb : d309787 q = 1) : d349539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309787, d349539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309787, d349539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309788 q = 1) : d349540 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309788, d349540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309788, d349540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309794 q = 1) : d349565 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309794, d349565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309794, d349565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101082 q ha hb
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309795 q = 1) : d349566 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309795, d349566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309795, d349566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309796 q = 1) : d349567 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309796, d349567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309796, d349567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309797 q = 1) : d349568 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309797, d349568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309797, d349568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309798 q = 1) : d349569 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309798, d349569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309798, d349569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d271214 q = 1) (hb : d309799 q = 1) : d349570 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309799, d349570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309799, d349570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro101084 (p : Pattern) (ha : d42338 p = 1) (hb : d271214 p = 1) : d349580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d271214 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42274 q = 1) (hb : d271214 q = 1) : d349516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101074 q ha hb
    | true =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42334 q = 1) (hb : d271214 q = 1) : d349576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42334, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42335 q = 1) (hb : d271214 q = 1) : d349577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42336 q = 1) (hb : d271214 q = 1) : d349578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42336, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42337 q = 1) (hb : d271214 q = 1) : d349579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42337, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42338 q = 1) (hb : d271214 q = 1) : d349580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42338, d349580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42338, d349580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101085 (p : Pattern) (ha : d42345 p = 1) (hb : d271214 p = 1) : d349587 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d271214 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42274 q = 1) (hb : d271214 q = 1) : d349516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101074 q ha hb
    | true =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42334 q = 1) (hb : d271214 q = 1) : d349576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42334, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42335 q = 1) (hb : d271214 q = 1) : d349577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42336 q = 1) (hb : d271214 q = 1) : d349578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42336, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42337 q = 1) (hb : d271214 q = 1) : d349579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42337, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d271214 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42281 q = 1) (hb : d271214 q = 1) : d349523 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42281, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101076 q ha hb
    | true =>
      simp only [d42281, d349523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42341 q = 1) (hb : d271214 q = 1) : d349583 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42341, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42341, d349583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42342 q = 1) (hb : d271214 q = 1) : d349584 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42342, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42342, d349584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42343 q = 1) (hb : d271214 q = 1) : d349585 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42343, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42343, d349585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42344 q = 1) (hb : d271214 q = 1) : d349586 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42344, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42344, d349586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42345 q = 1) (hb : d271214 q = 1) : d349587 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42345, d349587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42345, d349587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro101086 (p : Pattern) (ha : d42459 p = 1) (hb : d271214 p = 1) : d349668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d271214 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42274 q = 1) (hb : d271214 q = 1) : d349516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101074 q ha hb
    | true =>
      simp only [d42274, d349516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42334 q = 1) (hb : d271214 q = 1) : d349576 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42334, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42334, d349576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42335 q = 1) (hb : d271214 q = 1) : d349577 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42335, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42335, d349577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42336 q = 1) (hb : d271214 q = 1) : d349578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42336, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42336, d349578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42337 q = 1) (hb : d271214 q = 1) : d349579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42337, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42337, d349579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d271214 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42459 q = 1) (hb : d271214 q = 1) : d349668 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42459, d349668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42459, d349668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101087 (p : Pattern) (ha : d42350 p = 1) (hb : d271214 p = 1) : d349592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d271214 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d271214 q = 1) : d349512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d271214 q = 1) : d349513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42349 q = 1) (hb : d271214 q = 1) : d349591 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d349591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42349, d349591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42350 q = 1) (hb : d271214 q = 1) : d349592 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42350, d349592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42350, d349592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101088 (p : Pattern) (ha : d42357 p = 1) (hb : d271214 p = 1) : d349599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d271214 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d271214 q = 1) : d349512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42355 q = 1) (hb : d271214 q = 1) : d349597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d349597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42355, d349597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42356 q = 1) (hb : d271214 q = 1) : d349598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d349598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42356, d349598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42357 q = 1) (hb : d271214 q = 1) : d349599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42357, d349599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42357, d349599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101089 (p : Pattern) (ha : d42363 p = 1) (hb : d271214 p = 1) : d349603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42246 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42361 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42361, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15 q = 1) (hb : d271214 q = 1) : d15 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42247 q = 1) (hb : d271214 q = 1) : d1540 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42247, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42362 q = 1) (hb : d271214 q = 1) : d43420 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42362, d43420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42362, d43420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16 q = 1) (hb : d271214 q = 1) : d16 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d42248 q = 1) (hb : d271214 q = 1) : d42960 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42248, d42960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42248, d42960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42363 q = 1) (hb : d271214 q = 1) : d349603 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42363, d349603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42363, d349603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro101090 (p : Pattern) (ha : d42369 p = 1) (hb : d271214 p = 1) : d349609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42364 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42365 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42366 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42367 q = 1) (hb : d271214 q = 1) : d349607 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d349607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d349607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42368 q = 1) (hb : d271214 q = 1) : d349608 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d349608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42368, d349608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d271214 q = 1) : d21 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d42253 q = 1) (hb : d271214 q = 1) : d349495 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d349495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42253, d349495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42254 q = 1) (hb : d271214 q = 1) : d349496 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d349496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42254, d349496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42369 q = 1) (hb : d271214 q = 1) : d349609 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42369, d349609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42369, d349609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro101091 (p : Pattern) (ha : d42377 p = 1) (hb : d271214 p = 1) : d349617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42375 q = 1) (hb : d271214 q = 1) : d349615 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d349615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42375, d349615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42376 q = 1) (hb : d271214 q = 1) : d349616 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d349616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42376, d349616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d23 q = 1) (hb : d271214 q = 1) : d23 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42377 q = 1) (hb : d271214 q = 1) : d349617 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42377, d349617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42377, d349617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101092 (p : Pattern) (ha : d42383 p = 1) (hb : d271214 p = 1) : d349623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42370 q = 1) (hb : d271214 q = 1) : d349610 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101090 q ha hb
    | true =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42371 q = 1) (hb : d271214 q = 1) : d349611 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42372 q = 1) (hb : d271214 q = 1) : d349612 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d349612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42372, d349612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42373 q = 1) (hb : d271214 q = 1) : d349613 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d349613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d349613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42256 q = 1) (hb : d271214 q = 1) : d349498 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101071 q ha hb
    | true =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42257 q = 1) (hb : d271214 q = 1) : d349499 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42258 q = 1) (hb : d271214 q = 1) : d349500 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42258, d349500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42258, d349500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42259 q = 1) (hb : d271214 q = 1) : d349501 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42259, d349501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42259, d349501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42374 q = 1) (hb : d271214 q = 1) : d349614 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42374, d349614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42374, d349614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42378 q = 1) (hb : d271214 q = 1) : d349618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
    | true =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42379 q = 1) (hb : d271214 q = 1) : d349619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42380 q = 1) (hb : d271214 q = 1) : d349620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d349620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42380, d349620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42381 q = 1) (hb : d271214 q = 1) : d349621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d349621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42381, d349621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d271214 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d42382 q = 1) (hb : d271214 q = 1) : d349622 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d349622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42382, d349622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42383 q = 1) (hb : d271214 q = 1) : d349623 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42383, d349623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42383, d349623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro101093 (p : Pattern) (ha : d42389 p = 1) (hb : d271214 p = 1) : d349629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42384 q = 1) (hb : d271214 q = 1) : d349624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d349624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101092 q ha hb
    | true =>
      simp only [d42384, d349624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
  have h2 (q : Pattern) (ha : d42385 q = 1) (hb : d271214 q = 1) : d349625 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d349625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42385, d349625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42386 q = 1) (hb : d271214 q = 1) : d349626 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d349626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42386, d349626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d271214 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42262 q = 1) (hb : d271214 q = 1) : d349504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
    | true =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42263 q = 1) (hb : d271214 q = 1) : d349505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42264 q = 1) (hb : d271214 q = 1) : d349506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42387 q = 1) (hb : d271214 q = 1) : d349627 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d349627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d349627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d271214 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42265 q = 1) (hb : d271214 q = 1) : d349507 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42265, d349507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42265, d349507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42388 q = 1) (hb : d271214 q = 1) : d349628 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42388, d349628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42388, d349628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42389 q = 1) (hb : d271214 q = 1) : d349629 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42389, d349629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42389, d349629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro101094 (p : Pattern) (ha : d42395 p = 1) (hb : d271214 p = 1) : d349635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42390 q = 1) (hb : d271214 q = 1) : d349630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d349630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101093 q ha hb
    | true =>
      simp only [d42390, d349630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42391 q = 1) (hb : d271214 q = 1) : d349631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d349631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42391, d349631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42392 q = 1) (hb : d271214 q = 1) : d349632 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d349632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d349632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42393 q = 1) (hb : d271214 q = 1) : d349633 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d349633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d349633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42394 q = 1) (hb : d271214 q = 1) : d349634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d349634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d349634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42395 q = 1) (hb : d271214 q = 1) : d349635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42395, d349635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42395, d349635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101095 (p : Pattern) (ha : d42430 p = 1) (hb : d271214 p = 1) : d349641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42427 q = 1) (hb : d271214 q = 1) : d349638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d349638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d349638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42428 q = 1) (hb : d271214 q = 1) : d349639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d349639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d349639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42429 q = 1) (hb : d271214 q = 1) : d349640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d349640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d349640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42430 q = 1) (hb : d271214 q = 1) : d349641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42430, d349641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42430, d349641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101096 (p : Pattern) (ha : d271214 p = 1) (hb : d309809 p = 1) : d349647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d271214 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42351 q = 1) (hb : d271214 q = 1) : d349593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d349593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101087 q ha hb
    | true =>
      simp only [d42351, d349593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42352 q = 1) (hb : d271214 q = 1) : d349594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d349594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42352, d349594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42353 q = 1) (hb : d271214 q = 1) : d349595 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d349595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42353, d349595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42354 q = 1) (hb : d271214 q = 1) : d349596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d349596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42354, d349596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d271214 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42358 q = 1) (hb : d271214 q = 1) : d349600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d349600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101088 q ha hb
    | true =>
      simp only [d42358, d349600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42359 q = 1) (hb : d271214 q = 1) : d349601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d349601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42359, d349601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42360 q = 1) (hb : d271214 q = 1) : d349602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d349602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42360, d349602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42396 q = 1) (hb : d271214 q = 1) : d349636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d349636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101094 q ha hb
    | true =>
      simp only [d42396, d349636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101074 q ha hb
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309805 q = 1) : d349637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d349637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309805, d349637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d42431 q = 1) (hb : d271214 q = 1) : d349642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d349642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101095 q ha hb
    | true =>
      simp only [d42431, d349642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42432 q = 1) (hb : d271214 q = 1) : d349643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d349643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42432, d349643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309806 q = 1) : d349644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d349644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309806, d349644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309807 q = 1) : d349645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d349645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309807, d349645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309808 q = 1) : d349646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d349646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d309808, d349646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271214 q = 1) (hb : d309809 q = 1) : d349647 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309809, d349647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309809, d349647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro101097 (p : Pattern) (ha : d42437 p = 1) (hb : d271214 p = 1) : d349648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d271214 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d271214 q = 1) : d349512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42271 q = 1) (hb : d271214 q = 1) : d349513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42271, d349513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42349 q = 1) (hb : d271214 q = 1) : d349591 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42349, d349591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42349, d349591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42437 q = 1) (hb : d271214 q = 1) : d349648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42437, d349648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42437, d349648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro101098 (p : Pattern) (ha : d42442 p = 1) (hb : d271214 p = 1) : d349653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d271214 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42270 q = 1) (hb : d271214 q = 1) : d349512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42270, d349512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42355 q = 1) (hb : d271214 q = 1) : d349597 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42355, d349597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42355, d349597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42356 q = 1) (hb : d271214 q = 1) : d349598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42356, d349598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42356, d349598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42442 q = 1) (hb : d271214 q = 1) : d349653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42442, d349653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42442, d349653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro101099 (p : Pattern) (ha : d42446 p = 1) (hb : d271214 p = 1) : d349657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42390 q = 1) (hb : d271214 q = 1) : d349630 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42390, d349630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101093 q ha hb
    | true =>
      simp only [d42390, d349630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42391 q = 1) (hb : d271214 q = 1) : d349631 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42391, d349631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42391, d349631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42392 q = 1) (hb : d271214 q = 1) : d349632 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42392, d349632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42392, d349632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42393 q = 1) (hb : d271214 q = 1) : d349633 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42393, d349633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42393, d349633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42394 q = 1) (hb : d271214 q = 1) : d349634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42394, d349634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42394, d349634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42446 q = 1) (hb : d271214 q = 1) : d349657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42446, d349657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42446, d349657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101100 (p : Pattern) (ha : d42451 p = 1) (hb : d271214 p = 1) : d349660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42268 q = 1) (hb : d271214 q = 1) : d349510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101073 q ha hb
    | true =>
      simp only [d42268, d349510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42269 q = 1) (hb : d271214 q = 1) : d349511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42269, d349511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42427 q = 1) (hb : d271214 q = 1) : d349638 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42427, d349638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42427, d349638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42428 q = 1) (hb : d271214 q = 1) : d349639 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42428, d349639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42428, d349639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42429 q = 1) (hb : d271214 q = 1) : d349640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42429, d349640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42429, d349640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42451 q = 1) (hb : d271214 q = 1) : d349660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42451, d349660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42451, d349660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101101 (p : Pattern) (ha : d271214 p = 1) (hb : d309814 p = 1) : d349666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d271214 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42351 q = 1) (hb : d271214 q = 1) : d349593 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42351, d349593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101087 q ha hb
    | true =>
      simp only [d42351, d349593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42352 q = 1) (hb : d271214 q = 1) : d349594 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42352, d349594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42352, d349594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42353 q = 1) (hb : d271214 q = 1) : d349595 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42353, d349595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42353, d349595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42354 q = 1) (hb : d271214 q = 1) : d349596 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42354, d349596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42354, d349596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d271214 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42358 q = 1) (hb : d271214 q = 1) : d349600 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42358, d349600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101088 q ha hb
    | true =>
      simp only [d42358, d349600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42359 q = 1) (hb : d271214 q = 1) : d349601 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42359, d349601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42359, d349601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42360 q = 1) (hb : d271214 q = 1) : d349602 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42360, d349602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42360, d349602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42396 q = 1) (hb : d271214 q = 1) : d349636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42396, d349636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101094 q ha hb
    | true =>
      simp only [d42396, d349636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101074 q ha hb
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309805 q = 1) : d349637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309805, d349637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d309805, d349637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d42431 q = 1) (hb : d271214 q = 1) : d349642 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42431, d349642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101095 q ha hb
    | true =>
      simp only [d42431, d349642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42432 q = 1) (hb : d271214 q = 1) : d349643 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42432, d349643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42432, d349643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309806 q = 1) : d349644 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309806, d349644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309806, d349644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309807 q = 1) : d349645 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309807, d349645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d309807, d349645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309808 q = 1) : d349646 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309808, d349646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d309808, d349646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d271214 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d42438 q = 1) (hb : d271214 q = 1) : d349649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42438, d349649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101097 q ha hb
    | true =>
      simp only [d42438, d349649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42439 q = 1) (hb : d271214 q = 1) : d349650 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42439, d349650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42439, d349650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d42440 q = 1) (hb : d271214 q = 1) : d349651 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42440, d349651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42440, d349651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d42441 q = 1) (hb : d271214 q = 1) : d349652 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42441, d349652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42441, d349652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d271214 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d42443 q = 1) (hb : d271214 q = 1) : d349654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42443, d349654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101098 q ha hb
    | true =>
      simp only [d42443, d349654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d42444 q = 1) (hb : d271214 q = 1) : d349655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42444, d349655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42444, d349655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d42445 q = 1) (hb : d271214 q = 1) : d349656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42445, d349656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42445, d349656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d42447 q = 1) (hb : d271214 q = 1) : d349658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d349658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101099 q ha hb
    | true =>
      simp only [d42447, d349658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101076 q ha hb
  have h27 (q : Pattern) (ha : d271214 q = 1) (hb : d309810 q = 1) : d349659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d349659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d309810, d349659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d42452 q = 1) (hb : d271214 q = 1) : d349661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d349661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101100 q ha hb
    | true =>
      simp only [d42452, d349661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d42453 q = 1) (hb : d271214 q = 1) : d349662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d349662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d42453, d349662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d271214 q = 1) (hb : d309811 q = 1) : d349663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d349663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d309811, d349663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d271214 q = 1) (hb : d309812 q = 1) : d349664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309812, d349664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d309812, d349664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d271214 q = 1) (hb : d309813 q = 1) : d349665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309813, d349665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d309813, d349665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d271214 q = 1) (hb : d309814 q = 1) : d349666 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309814, d349666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309814, d349666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro101102 (p : Pattern) (ha : d271214 p = 1) (hb : d309821 p = 1) : d349675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42447 q = 1) (hb : d271214 q = 1) : d349658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42447, d349658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101099 q ha hb
    | true =>
      simp only [d42447, d349658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101076 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309810 q = 1) : d349659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309810, d349659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309810, d349659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d42452 q = 1) (hb : d271214 q = 1) : d349661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42452, d349661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101100 q ha hb
    | true =>
      simp only [d42452, d349661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42453 q = 1) (hb : d271214 q = 1) : d349662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42453, d349662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42453, d349662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309811 q = 1) : d349663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309811, d349663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309811, d349663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309819 q = 1) : d349673 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309819, d349673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309819, d349673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309820 q = 1) : d349674 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309820, d349674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309820, d349674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309821 q = 1) : d349675 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309821, d349675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309821, d349675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101103 (p : Pattern) (ha : d42482 p = 1) (hb : d271214 p = 1) : d349691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42472 q = 1) (hb : d271214 q = 1) : d349681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d349681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42472, d349681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101090 q ha hb
  have h2 (q : Pattern) (ha : d42370 q = 1) (hb : d271214 q = 1) : d349610 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101090 q ha hb
    | true =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42473 q = 1) (hb : d271214 q = 1) : d349682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d349682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d349682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42371 q = 1) (hb : d271214 q = 1) : d349611 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42474 q = 1) (hb : d271214 q = 1) : d349683 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d349683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d349683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42475 q = 1) (hb : d271214 q = 1) : d349684 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d349684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d349684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42299 q = 1) (hb : d271214 q = 1) : d349541 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42299, d349541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42299, d349541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101071 q ha hb
  have h8 (q : Pattern) (ha : d42256 q = 1) (hb : d271214 q = 1) : d349498 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101071 q ha hb
    | true =>
      simp only [d42256, d349498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42300 q = 1) (hb : d271214 q = 1) : d349542 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42300, d349542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42300, d349542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42257 q = 1) (hb : d271214 q = 1) : d349499 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42257, d349499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42301 q = 1) (hb : d271214 q = 1) : d349543 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42301, d349543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42301, d349543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42302 q = 1) (hb : d271214 q = 1) : d349544 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42302, d349544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42302, d349544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42476 q = 1) (hb : d271214 q = 1) : d349685 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42476, d349685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42476, d349685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42477 q = 1) (hb : d271214 q = 1) : d349686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d349686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42477, d349686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
  have h15 (q : Pattern) (ha : d42378 q = 1) (hb : d271214 q = 1) : d349618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
    | true =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42478 q = 1) (hb : d271214 q = 1) : d349687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d349687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42478, d349687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42379 q = 1) (hb : d271214 q = 1) : d349619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42479 q = 1) (hb : d271214 q = 1) : d349688 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d349688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42479, d349688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42480 q = 1) (hb : d271214 q = 1) : d349689 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d349689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42480, d349689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d271214 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d42481 q = 1) (hb : d271214 q = 1) : d349690 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d349690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42481, d349690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d42482 q = 1) (hb : d271214 q = 1) : d349691 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42482, d349691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42482, d349691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro101104 (p : Pattern) (ha : d42488 p = 1) (hb : d271214 p = 1) : d349697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42483 q = 1) (hb : d271214 q = 1) : d349692 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d349692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101103 q ha hb
    | true =>
      simp only [d42483, d349692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
  have h2 (q : Pattern) (ha : d42484 q = 1) (hb : d271214 q = 1) : d349693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d349693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42484, d349693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42485 q = 1) (hb : d271214 q = 1) : d349694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d349694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42485, d349694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d271214 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42305 q = 1) (hb : d271214 q = 1) : d349547 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
    | true =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42306 q = 1) (hb : d271214 q = 1) : d349548 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42307 q = 1) (hb : d271214 q = 1) : d349549 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42486 q = 1) (hb : d271214 q = 1) : d349695 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d349695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d349695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d271214 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42308 q = 1) (hb : d271214 q = 1) : d349550 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42308, d349550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42308, d349550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42487 q = 1) (hb : d271214 q = 1) : d349696 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42487, d349696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42487, d349696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42488 q = 1) (hb : d271214 q = 1) : d349697 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42488, d349697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42488, d349697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro101105 (p : Pattern) (ha : d42494 p = 1) (hb : d271214 p = 1) : d349703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42489 q = 1) (hb : d271214 q = 1) : d349698 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42489, d349698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101104 q ha hb
    | true =>
      simp only [d42489, d349698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42490 q = 1) (hb : d271214 q = 1) : d349699 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42490, d349699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42490, d349699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42311 q = 1) (hb : d271214 q = 1) : d349553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d349553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101080 q ha hb
    | true =>
      simp only [d42311, d349553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42312 q = 1) (hb : d271214 q = 1) : d349554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d349554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42312, d349554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42491 q = 1) (hb : d271214 q = 1) : d349700 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42491, d349700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42491, d349700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42492 q = 1) (hb : d271214 q = 1) : d349701 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42492, d349701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42492, d349701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42493 q = 1) (hb : d271214 q = 1) : d349702 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42493, d349702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42493, d349702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42494 q = 1) (hb : d271214 q = 1) : d349703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42494, d349703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42494, d349703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101106 (p : Pattern) (ha : d42519 p = 1) (hb : d271214 p = 1) : d349709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42311 q = 1) (hb : d271214 q = 1) : d349553 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42311, d349553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101080 q ha hb
    | true =>
      simp only [d42311, d349553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42312 q = 1) (hb : d271214 q = 1) : d349554 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42312, d349554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42312, d349554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42516 q = 1) (hb : d271214 q = 1) : d349706 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42516, d349706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42516, d349706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42517 q = 1) (hb : d271214 q = 1) : d349707 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42517, d349707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42517, d349707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42518 q = 1) (hb : d271214 q = 1) : d349708 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42518, d349708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42518, d349708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42519 q = 1) (hb : d271214 q = 1) : d349709 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42519, d349709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42519, d349709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101107 (p : Pattern) (ha : d271214 p = 1) (hb : d309831 p = 1) : d349715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42495 q = 1) (hb : d271214 q = 1) : d349704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42495, d349704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101105 q ha hb
    | true =>
      simp only [d42495, d349704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101081 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309827 q = 1) : d349705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309827, d349705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309827, d349705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d42520 q = 1) (hb : d271214 q = 1) : d349710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42520, d349710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101106 q ha hb
    | true =>
      simp only [d42520, d349710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42521 q = 1) (hb : d271214 q = 1) : d349711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42521, d349711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42521, d349711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309828 q = 1) : d349712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309828, d349712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309828, d349712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309829 q = 1) : d349713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309829, d349713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309829, d349713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309830 q = 1) : d349714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309830, d349714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309830, d349714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309831 q = 1) : d349715 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309831, d349715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309831, d349715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101108 (p : Pattern) (ha : d271214 p = 1) (hb : d309837 p = 1) : d349721 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42339 q = 1) (hb : d271214 q = 1) : d349581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42339, d349581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42339, d349581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101084 q ha hb
  have h2 (q : Pattern) (ha : d42340 q = 1) (hb : d271214 q = 1) : d349582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42340, d349582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42340, d349582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42346 q = 1) (hb : d271214 q = 1) : d349588 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42346, d349588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101084 q ha hb
    | true =>
      simp only [d42346, d349588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101085 q ha hb
  have h4 (q : Pattern) (ha : d42347 q = 1) (hb : d271214 q = 1) : d349589 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42347, d349589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42347, d349589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42348 q = 1) (hb : d271214 q = 1) : d349590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42348, d349590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42348, d349590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309815 q = 1) : d349667 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309815, d349667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101096 q ha hb
    | true =>
      simp only [d309815, d349667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101101 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d271214 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42460 q = 1) (hb : d271214 q = 1) : d349669 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42460, d349669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101086 q ha hb
    | true =>
      simp only [d42460, d349669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309816 q = 1) : d349670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309816, d349670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309816, d349670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d271214 q = 1) (hb : d309817 q = 1) : d349671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309817, d349671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309817, d349671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309818 q = 1) : d349672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309818, d349672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d309818, d349672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309822 q = 1) : d349676 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309822, d349676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309822, d349676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101102 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d271214 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309823 q = 1) : d349677 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309823, d349677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d309823, d349677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309824 q = 1) : d349678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309824, d349678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309824, d349678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309825 q = 1) : d349679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309825, d349679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d309825, d349679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d271214 q = 1) (hb : d309826 q = 1) : d349680 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309826, d349680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309826, d349680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d271214 q = 1) (hb : d309832 q = 1) : d349716 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309832, d349716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309832, d349716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101107 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d271214 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d271214 q = 1) (hb : d309833 q = 1) : d349717 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309833, d349717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d309833, d349717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d271214 q = 1) (hb : d309834 q = 1) : d349718 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309834, d349718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309834, d349718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d271214 q = 1) (hb : d309835 q = 1) : d349719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309835, d349719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309835, d349719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d271214 q = 1) (hb : d309836 q = 1) : d349720 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309836, d349720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d309836, d349720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d271214 q = 1) (hb : d309837 q = 1) : d349721 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309837, d349721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309837, d349721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro101109 (p : Pattern) (ha : d271214 p = 1) (hb : d309843 p = 1) : d349727 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d271214 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309800 q = 1) : d349571 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309800, d349571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309800, d349571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101083 q ha hb
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d309801 q = 1) : d349572 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309801, d349572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309801, d349572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d309802 q = 1) : d349573 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309802, d349573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309802, d349573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309803 q = 1) : d349574 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309803, d349574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309803, d349574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309804 q = 1) : d349575 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309804, d349575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309804, d349575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309838 q = 1) : d349722 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309838, d349722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309838, d349722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101108 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309839 q = 1) : d349723 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309839, d349723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309839, d349723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309840 q = 1) : d349724 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309840, d349724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309840, d349724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d271214 q = 1) (hb : d309841 q = 1) : d349725 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309841, d349725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309841, d349725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309842 q = 1) : d349726 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309842, d349726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309842, d349726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309843 q = 1) : d349727 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309843, d349727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309843, d349727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro101110 (p : Pattern) (ha : d42540 p = 1) (hb : d271214 p = 1) : d349730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42384 q = 1) (hb : d271214 q = 1) : d349624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d349624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101092 q ha hb
    | true =>
      simp only [d42384, d349624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
  have h2 (q : Pattern) (ha : d42385 q = 1) (hb : d271214 q = 1) : d349625 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d349625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42385, d349625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42386 q = 1) (hb : d271214 q = 1) : d349626 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d349626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42386, d349626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d271214 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42262 q = 1) (hb : d271214 q = 1) : d349504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
    | true =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42263 q = 1) (hb : d271214 q = 1) : d349505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42264 q = 1) (hb : d271214 q = 1) : d349506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42387 q = 1) (hb : d271214 q = 1) : d349627 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d349627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42387, d349627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42538 q = 1) (hb : d271214 q = 1) : d349728 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d349728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42538, d349728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42539 q = 1) (hb : d271214 q = 1) : d349729 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42539, d349729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42539, d349729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42540 q = 1) (hb : d271214 q = 1) : d349730 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42540, d349730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42540, d349730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro101111 (p : Pattern) (ha : d42544 p = 1) (hb : d271214 p = 1) : d349734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d271214 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42262 q = 1) (hb : d271214 q = 1) : d349504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
    | true =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42263 q = 1) (hb : d271214 q = 1) : d349505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42264 q = 1) (hb : d271214 q = 1) : d349506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42538 q = 1) (hb : d271214 q = 1) : d349728 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42538, d349728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42538, d349728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42543 q = 1) (hb : d271214 q = 1) : d349733 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42543, d349733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42543, d349733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42544 q = 1) (hb : d271214 q = 1) : d349734 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42544, d349734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42544, d349734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro101112 (p : Pattern) (ha : d42550 p = 1) (hb : d271214 p = 1) : d349740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d271214 q = 1) : d349737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d271214 q = 1) : d349738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42549 q = 1) (hb : d271214 q = 1) : d349739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d349739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d349739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42550 q = 1) (hb : d271214 q = 1) : d349740 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42550, d349740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42550, d349740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101113 (p : Pattern) (ha : d42554 p = 1) (hb : d271214 p = 1) : d349744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d271214 q = 1) : d349741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d271214 q = 1) : d349742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42553 q = 1) (hb : d271214 q = 1) : d349743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d349743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d349743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42554 q = 1) (hb : d271214 q = 1) : d349744 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42554, d349744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42554, d349744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101114 (p : Pattern) (ha : d42560 p = 1) (hb : d271214 p = 1) : d349750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42555 q = 1) (hb : d271214 q = 1) : d349745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101112 q ha hb
    | true =>
      simp only [d42555, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101113 q ha hb
  have h2 (q : Pattern) (ha : d42556 q = 1) (hb : d271214 q = 1) : d349746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42556, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42557 q = 1) (hb : d271214 q = 1) : d349747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42558 q = 1) (hb : d271214 q = 1) : d349748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42558, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42559 q = 1) (hb : d271214 q = 1) : d349749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42559, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42560 q = 1) (hb : d271214 q = 1) : d349750 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42560, d349750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42560, d349750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101115 (p : Pattern) (ha : d42563 p = 1) (hb : d271214 p = 1) : d349753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d271214 q = 1) : d349737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d271214 q = 1) : d349738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42549 q = 1) (hb : d271214 q = 1) : d349739 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42549, d349739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42549, d349739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42563 q = 1) (hb : d271214 q = 1) : d349753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42563, d349753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42563, d349753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101116 (p : Pattern) (ha : d42564 p = 1) (hb : d271214 p = 1) : d349754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d271214 q = 1) : d349741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d271214 q = 1) : d349742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42553 q = 1) (hb : d271214 q = 1) : d349743 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42553, d349743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42553, d349743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42564 q = 1) (hb : d271214 q = 1) : d349754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42564, d349754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42564, d349754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101117 (p : Pattern) (ha : d42570 p = 1) (hb : d271214 p = 1) : d349760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42555 q = 1) (hb : d271214 q = 1) : d349745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101112 q ha hb
    | true =>
      simp only [d42555, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101113 q ha hb
  have h2 (q : Pattern) (ha : d42556 q = 1) (hb : d271214 q = 1) : d349746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42556, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42557 q = 1) (hb : d271214 q = 1) : d349747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42558 q = 1) (hb : d271214 q = 1) : d349748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42558, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42559 q = 1) (hb : d271214 q = 1) : d349749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42559, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42565 q = 1) (hb : d271214 q = 1) : d349755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42565, d349755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101115 q ha hb
    | true =>
      simp only [d42565, d349755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101116 q ha hb
  have h7 (q : Pattern) (ha : d42566 q = 1) (hb : d271214 q = 1) : d349756 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42566, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42566, d349756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42567 q = 1) (hb : d271214 q = 1) : d349757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42567, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42567, d349757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42568 q = 1) (hb : d271214 q = 1) : d349758 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42568, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42568, d349758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42569 q = 1) (hb : d271214 q = 1) : d349759 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42569, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42569, d349759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42570 q = 1) (hb : d271214 q = 1) : d349760 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42570, d349760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42570, d349760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101118 (p : Pattern) (ha : d42730 p = 1) (hb : d271214 p = 1) : d349866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42555 q = 1) (hb : d271214 q = 1) : d349745 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42555, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101112 q ha hb
    | true =>
      simp only [d42555, d349745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101113 q ha hb
  have h2 (q : Pattern) (ha : d42556 q = 1) (hb : d271214 q = 1) : d349746 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42556, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42556, d349746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42557 q = 1) (hb : d271214 q = 1) : d349747 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42557, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42557, d349747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42558 q = 1) (hb : d271214 q = 1) : d349748 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42558, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42558, d349748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42559 q = 1) (hb : d271214 q = 1) : d349749 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42559, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42559, d349749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42725 q = 1) (hb : d271214 q = 1) : d349861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d349861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101113 q ha hb
    | true =>
      simp only [d42725, d349861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42726 q = 1) (hb : d271214 q = 1) : d349862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d349862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42726, d349862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42727 q = 1) (hb : d271214 q = 1) : d349863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d349863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42727, d349863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42728 q = 1) (hb : d271214 q = 1) : d349864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d349864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42728, d349864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42729 q = 1) (hb : d271214 q = 1) : d349865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d349865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42729, d349865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42730 q = 1) (hb : d271214 q = 1) : d349866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42730, d349866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42730, d349866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101119 (p : Pattern) (ha : d42736 p = 1) (hb : d271214 p = 1) : d349872 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42725 q = 1) (hb : d271214 q = 1) : d349861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42725, d349861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101113 q ha hb
    | true =>
      simp only [d42725, d349861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42726 q = 1) (hb : d271214 q = 1) : d349862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42726, d349862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42726, d349862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42727 q = 1) (hb : d271214 q = 1) : d349863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42727, d349863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42727, d349863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42728 q = 1) (hb : d271214 q = 1) : d349864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42728, d349864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42728, d349864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42729 q = 1) (hb : d271214 q = 1) : d349865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42729, d349865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42729, d349865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42731 q = 1) (hb : d271214 q = 1) : d349867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d349867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101116 q ha hb
    | true =>
      simp only [d42731, d349867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42732 q = 1) (hb : d271214 q = 1) : d349868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d349868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42732, d349868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42733 q = 1) (hb : d271214 q = 1) : d349869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d349869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42733, d349869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42734 q = 1) (hb : d271214 q = 1) : d349870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d349870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42734, d349870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42735 q = 1) (hb : d271214 q = 1) : d349871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d349871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42735, d349871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42736 q = 1) (hb : d271214 q = 1) : d349872 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42736, d349872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42736, d349872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101120 (p : Pattern) (ha : d42745 p = 1) (hb : d271214 p = 1) : d349881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42731 q = 1) (hb : d271214 q = 1) : d349867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42731, d349867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101116 q ha hb
    | true =>
      simp only [d42731, d349867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42732 q = 1) (hb : d271214 q = 1) : d349868 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42732, d349868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42732, d349868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42733 q = 1) (hb : d271214 q = 1) : d349869 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42733, d349869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42733, d349869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42734 q = 1) (hb : d271214 q = 1) : d349870 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42734, d349870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42734, d349870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42735 q = 1) (hb : d271214 q = 1) : d349871 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42735, d349871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42735, d349871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42745 q = 1) (hb : d271214 q = 1) : d349881 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42745, d349881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42745, d349881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101121 (p : Pattern) (ha : d42788 p = 1) (hb : d271214 p = 1) : d349924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d271214 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42305 q = 1) (hb : d271214 q = 1) : d349547 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
    | true =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42306 q = 1) (hb : d271214 q = 1) : d349548 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42307 q = 1) (hb : d271214 q = 1) : d349549 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42778 q = 1) (hb : d271214 q = 1) : d349914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d349914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42778, d349914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42787 q = 1) (hb : d271214 q = 1) : d349923 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42787, d349923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42787, d349923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42788 q = 1) (hb : d271214 q = 1) : d349924 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42788, d349924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42788, d349924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro101122 (p : Pattern) (ha : d42844 p = 1) (hb : d271214 p = 1) : d349947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42789 q = 1) (hb : d271214 q = 1) : d349925 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d349925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101121 q ha hb
    | true =>
      simp only [d42789, d349925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42790 q = 1) (hb : d271214 q = 1) : d349926 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d349926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42790, d349926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42841 q = 1) (hb : d271214 q = 1) : d349944 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42841, d349944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42841, d349944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42842 q = 1) (hb : d271214 q = 1) : d349945 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42842, d349945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42842, d349945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42843 q = 1) (hb : d271214 q = 1) : d349946 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42843, d349946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42843, d349946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42844 q = 1) (hb : d271214 q = 1) : d349947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42844, d349947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42844, d349947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101123 (p : Pattern) (ha : d42850 p = 1) (hb : d271214 p = 1) : d349953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42845 q = 1) (hb : d271214 q = 1) : d349948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42845, d349948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101122 q ha hb
    | true =>
      simp only [d42845, d349948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42846 q = 1) (hb : d271214 q = 1) : d349949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42846, d349949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42846, d349949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42847 q = 1) (hb : d271214 q = 1) : d349950 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42847, d349950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42847, d349950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42848 q = 1) (hb : d271214 q = 1) : d349951 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42848, d349951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42848, d349951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42849 q = 1) (hb : d271214 q = 1) : d349952 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42849, d349952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42849, d349952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42850 q = 1) (hb : d271214 q = 1) : d349953 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42850, d349953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42850, d349953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101124 (p : Pattern) (ha : d42575 p = 1) (hb : d271214 p = 1) : d349765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d271214 q = 1) : d349737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d271214 q = 1) : d349738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42574 q = 1) (hb : d271214 q = 1) : d349764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d349764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42574, d349764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42575 q = 1) (hb : d271214 q = 1) : d349765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42575, d349765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42575, d349765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101125 (p : Pattern) (ha : d42577 p = 1) (hb : d271214 p = 1) : d349767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d271214 q = 1) : d349741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d271214 q = 1) : d349742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42576 q = 1) (hb : d271214 q = 1) : d349766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d349766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42576, d349766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42577 q = 1) (hb : d271214 q = 1) : d349767 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42577, d349767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42577, d349767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101126 (p : Pattern) (ha : d42584 p = 1) (hb : d271214 p = 1) : d349774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d271214 q = 1) : d349737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42582 q = 1) (hb : d271214 q = 1) : d349772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d349772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42582, d349772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42583 q = 1) (hb : d271214 q = 1) : d349773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d349773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d349773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42584 q = 1) (hb : d271214 q = 1) : d349774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42584, d349774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42584, d349774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101127 (p : Pattern) (ha : d42587 p = 1) (hb : d271214 p = 1) : d349777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d271214 q = 1) : d349741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42585 q = 1) (hb : d271214 q = 1) : d349775 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d349775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42585, d349775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42586 q = 1) (hb : d271214 q = 1) : d349776 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d349776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d349776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42587 q = 1) (hb : d271214 q = 1) : d349777 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42587, d349777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42587, d349777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101128 (p : Pattern) (ha : d42594 p = 1) (hb : d271214 p = 1) : d349781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34366 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42591 q = 1) (hb : d271214 q = 1) : d42935 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42591, d42935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42591, d42935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1519 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42592 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42592, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42592, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d42246 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d15 q = 1) (hb : d271214 q = 1) : d15 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d42247 q = 1) (hb : d271214 q = 1) : d1540 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42247, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42247, d1540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42593 q = 1) (hb : d271214 q = 1) : d43420 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42593, d43420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42593, d43420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42594 q = 1) (hb : d271214 q = 1) : d349781 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42594, d349781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42594, d349781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101129 (p : Pattern) (ha : d42601 p = 1) (hb : d271214 p = 1) : d349785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42246 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42361 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42361, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42598 q = 1) (hb : d271214 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42599 q = 1) (hb : d271214 q = 1) : d43873 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42599, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42599, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16 q = 1) (hb : d271214 q = 1) : d16 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d42600 q = 1) (hb : d271214 q = 1) : d9579 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42600, d9579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42600, d9579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42601 q = 1) (hb : d271214 q = 1) : d349785 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42601, d349785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42601, d349785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro101130 (p : Pattern) (ha : d42607 p = 1) (hb : d271214 p = 1) : d349791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42595 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42596 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42364 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42365 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42597 q = 1) (hb : d271214 q = 1) : d349784 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42597, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42602 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101129 q ha hb
    | true =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42603 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42604 q = 1) (hb : d271214 q = 1) : d349788 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42605 q = 1) (hb : d271214 q = 1) : d349789 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42605, d349789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42605, d349789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42606 q = 1) (hb : d271214 q = 1) : d349790 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42606, d349790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42606, d349790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42366 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h14 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42367 q = 1) (hb : d271214 q = 1) : d349607 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d349607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42367, d349607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42368 q = 1) (hb : d271214 q = 1) : d349608 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d349608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42368, d349608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42607 q = 1) (hb : d271214 q = 1) : d349791 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42607, d349791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42607, d349791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro101131 (p : Pattern) (ha : d42612 p = 1) (hb : d271214 p = 1) : d349796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42364 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42365 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42366 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42367 q = 1) (hb : d271214 q = 1) : d349607 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42367, d349607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42367, d349607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42368 q = 1) (hb : d271214 q = 1) : d349608 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42368, d349608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42368, d349608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42375 q = 1) (hb : d271214 q = 1) : d349615 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d349615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42375, d349615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42376 q = 1) (hb : d271214 q = 1) : d349616 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d349616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42376, d349616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42612 q = 1) (hb : d271214 q = 1) : d349796 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42612, d349796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42612, d349796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro101132 (p : Pattern) (ha : d42620 p = 1) (hb : d271214 p = 1) : d349804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42364 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42365 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42366 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42366, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42618 q = 1) (hb : d271214 q = 1) : d349802 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42618, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42618, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42619 q = 1) (hb : d271214 q = 1) : d349803 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42619, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42619, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42375 q = 1) (hb : d271214 q = 1) : d349615 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42375, d349615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42375, d349615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42376 q = 1) (hb : d271214 q = 1) : d349616 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42376, d349616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42376, d349616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42620 q = 1) (hb : d271214 q = 1) : d349804 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42620, d349804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42620, d349804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro101133 (p : Pattern) (ha : d42626 p = 1) (hb : d271214 p = 1) : d349810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42608 q = 1) (hb : d271214 q = 1) : d349792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101130 q ha hb
    | true =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42609 q = 1) (hb : d271214 q = 1) : d349793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42610 q = 1) (hb : d271214 q = 1) : d349794 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d349794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42610, d349794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42611 q = 1) (hb : d271214 q = 1) : d349795 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d349795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d349795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42613 q = 1) (hb : d271214 q = 1) : d349797 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101131 q ha hb
    | true =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42614 q = 1) (hb : d271214 q = 1) : d349798 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42615 q = 1) (hb : d271214 q = 1) : d349799 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d349799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42615, d349799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42616 q = 1) (hb : d271214 q = 1) : d349800 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d349800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d349800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42617 q = 1) (hb : d271214 q = 1) : d349801 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d349801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d349801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42623 q = 1) (hb : d271214 q = 1) : d349807 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42624 q = 1) (hb : d271214 q = 1) : d349808 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42378 q = 1) (hb : d271214 q = 1) : d349618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
    | true =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42379 q = 1) (hb : d271214 q = 1) : d349619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42380 q = 1) (hb : d271214 q = 1) : d349620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d349620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42380, d349620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42381 q = 1) (hb : d271214 q = 1) : d349621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d349621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42381, d349621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42625 q = 1) (hb : d271214 q = 1) : d349809 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42625, d349809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42625, d349809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42626 q = 1) (hb : d271214 q = 1) : d349810 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42626, d349810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42626, d349810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro101134 (p : Pattern) (ha : d42630 p = 1) (hb : d271214 p = 1) : d349814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42378 q = 1) (hb : d271214 q = 1) : d349618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
    | true =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42379 q = 1) (hb : d271214 q = 1) : d349619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42380 q = 1) (hb : d271214 q = 1) : d349620 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42380, d349620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42380, d349620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42381 q = 1) (hb : d271214 q = 1) : d349621 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42381, d349621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42381, d349621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d271214 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42382 q = 1) (hb : d271214 q = 1) : d349622 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42382, d349622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42382, d349622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d271214 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42630 q = 1) (hb : d271214 q = 1) : d349814 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42630, d349814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42630, d349814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101135 (p : Pattern) (ha : d42636 p = 1) (hb : d271214 p = 1) : d349820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42627 q = 1) (hb : d271214 q = 1) : d349811 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42627, d349811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101133 q ha hb
    | true =>
      simp only [d42627, d349811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101092 q ha hb
  have h2 (q : Pattern) (ha : d42628 q = 1) (hb : d271214 q = 1) : d349812 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42628, d349812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42628, d349812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42629 q = 1) (hb : d271214 q = 1) : d349813 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42629, d349813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42629, d349813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42631 q = 1) (hb : d271214 q = 1) : d349815 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42631, d349815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101092 q ha hb
    | true =>
      simp only [d42631, d349815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101134 q ha hb
  have h5 (q : Pattern) (ha : d42632 q = 1) (hb : d271214 q = 1) : d349816 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42632, d349816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42632, d349816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42633 q = 1) (hb : d271214 q = 1) : d349817 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42633, d349817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42633, d349817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42634 q = 1) (hb : d271214 q = 1) : d349818 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42634, d349818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42634, d349818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42384 q = 1) (hb : d271214 q = 1) : d349624 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42384, d349624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101092 q ha hb
    | true =>
      simp only [d42384, d349624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
  have h9 (q : Pattern) (ha : d42385 q = 1) (hb : d271214 q = 1) : d349625 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42385, d349625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42385, d349625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42386 q = 1) (hb : d271214 q = 1) : d349626 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42386, d349626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42386, d349626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d271214 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d42262 q = 1) (hb : d271214 q = 1) : d349504 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101072 q ha hb
    | true =>
      simp only [d42262, d349504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42263 q = 1) (hb : d271214 q = 1) : d349505 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42263, d349505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42264 q = 1) (hb : d271214 q = 1) : d349506 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42264, d349506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42387 q = 1) (hb : d271214 q = 1) : d349627 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42387, d349627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42387, d349627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42635 q = 1) (hb : d271214 q = 1) : d349819 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42635, d349819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42635, d349819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42636 q = 1) (hb : d271214 q = 1) : d349820 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42636, d349820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42636, d349820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro101136 (p : Pattern) (ha : d42642 p = 1) (hb : d271214 p = 1) : d349826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42637 q = 1) (hb : d271214 q = 1) : d349821 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d349821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101135 q ha hb
    | true =>
      simp only [d42637, d349821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42638 q = 1) (hb : d271214 q = 1) : d349822 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d349822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42638, d349822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42639 q = 1) (hb : d271214 q = 1) : d349823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d349823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d349823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42640 q = 1) (hb : d271214 q = 1) : d349824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d349824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d349824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42641 q = 1) (hb : d271214 q = 1) : d349825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d349825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d349825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42642 q = 1) (hb : d271214 q = 1) : d349826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42642, d349826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42642, d349826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101137 (p : Pattern) (ha : d42693 p = 1) (hb : d271214 p = 1) : d349832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42690 q = 1) (hb : d271214 q = 1) : d349829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d349829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d349829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42691 q = 1) (hb : d271214 q = 1) : d349830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d349830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d349830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42692 q = 1) (hb : d271214 q = 1) : d349831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d349831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d349831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42693 q = 1) (hb : d271214 q = 1) : d349832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42693, d349832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42693, d349832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101138 (p : Pattern) (ha : d271214 p = 1) (hb : d309848 p = 1) : d349838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42578 q = 1) (hb : d271214 q = 1) : d349768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d349768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101124 q ha hb
    | true =>
      simp only [d42578, d349768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101125 q ha hb
  have h2 (q : Pattern) (ha : d42579 q = 1) (hb : d271214 q = 1) : d349769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d349769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42579, d349769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42580 q = 1) (hb : d271214 q = 1) : d349770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d349770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d349770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42581 q = 1) (hb : d271214 q = 1) : d349771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d349771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42581, d349771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42588 q = 1) (hb : d271214 q = 1) : d349778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d349778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101126 q ha hb
    | true =>
      simp only [d42588, d349778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101127 q ha hb
  have h6 (q : Pattern) (ha : d42589 q = 1) (hb : d271214 q = 1) : d349779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d349779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42589, d349779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42590 q = 1) (hb : d271214 q = 1) : d349780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d349780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d349780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42643 q = 1) (hb : d271214 q = 1) : d349827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d349827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101136 q ha hb
    | true =>
      simp only [d42643, d349827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101112 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309844 q = 1) : d349828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d349828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d309844, d349828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d42694 q = 1) (hb : d271214 q = 1) : d349833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d349833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101137 q ha hb
    | true =>
      simp only [d42694, d349833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42695 q = 1) (hb : d271214 q = 1) : d349834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d349834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d349834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309845 q = 1) : d349835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d349835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d349835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309846 q = 1) : d349836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d349836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309846, d349836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309847 q = 1) : d349837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d349837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309847, d349837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309848 q = 1) : d349838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309848, d349838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309848, d349838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101139 (p : Pattern) (ha : d42700 p = 1) (hb : d271214 p = 1) : d349839 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d271214 q = 1) : d349737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42548 q = 1) (hb : d271214 q = 1) : d349738 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42548, d349738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42574 q = 1) (hb : d271214 q = 1) : d349764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42574, d349764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42574, d349764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42700 q = 1) (hb : d271214 q = 1) : d349839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42700, d349839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42700, d349839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101140 (p : Pattern) (ha : d42701 p = 1) (hb : d271214 p = 1) : d349840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d271214 q = 1) : d349741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42552 q = 1) (hb : d271214 q = 1) : d349742 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42552, d349742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42576 q = 1) (hb : d271214 q = 1) : d349766 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42576, d349766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42576, d349766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42701 q = 1) (hb : d271214 q = 1) : d349840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42701, d349840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42701, d349840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101141 (p : Pattern) (ha : d42706 p = 1) (hb : d271214 p = 1) : d349845 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42547 q = 1) (hb : d271214 q = 1) : d349737 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42547, d349737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42582 q = 1) (hb : d271214 q = 1) : d349772 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42582, d349772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42582, d349772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42583 q = 1) (hb : d271214 q = 1) : d349773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42583, d349773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42583, d349773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42706 q = 1) (hb : d271214 q = 1) : d349845 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42706, d349845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42706, d349845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101142 (p : Pattern) (ha : d42707 p = 1) (hb : d271214 p = 1) : d349846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42545 q = 1) (hb : d271214 q = 1) : d349735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101111 q ha hb
    | true =>
      simp only [d42545, d349735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42546 q = 1) (hb : d271214 q = 1) : d349736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42546, d349736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42551 q = 1) (hb : d271214 q = 1) : d349741 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42551, d349741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42585 q = 1) (hb : d271214 q = 1) : d349775 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42585, d349775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42585, d349775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42586 q = 1) (hb : d271214 q = 1) : d349776 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42586, d349776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42586, d349776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42707 q = 1) (hb : d271214 q = 1) : d349846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42707, d349846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42707, d349846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101143 (p : Pattern) (ha : d42711 p = 1) (hb : d271214 p = 1) : d349850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42637 q = 1) (hb : d271214 q = 1) : d349821 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42637, d349821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101135 q ha hb
    | true =>
      simp only [d42637, d349821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42638 q = 1) (hb : d271214 q = 1) : d349822 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42638, d349822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42638, d349822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42639 q = 1) (hb : d271214 q = 1) : d349823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42639, d349823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42639, d349823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42640 q = 1) (hb : d271214 q = 1) : d349824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42640, d349824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42640, d349824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42641 q = 1) (hb : d271214 q = 1) : d349825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42641, d349825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42641, d349825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42711 q = 1) (hb : d271214 q = 1) : d349850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42711, d349850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42711, d349850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101144 (p : Pattern) (ha : d42717 p = 1) (hb : d271214 p = 1) : d349853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42541 q = 1) (hb : d271214 q = 1) : d349731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101110 q ha hb
    | true =>
      simp only [d42541, d349731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42542 q = 1) (hb : d271214 q = 1) : d349732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42542, d349732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42690 q = 1) (hb : d271214 q = 1) : d349829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42690, d349829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42690, d349829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42691 q = 1) (hb : d271214 q = 1) : d349830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42691, d349830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42691, d349830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42692 q = 1) (hb : d271214 q = 1) : d349831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42692, d349831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42692, d349831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42717 q = 1) (hb : d271214 q = 1) : d349853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42717, d349853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42717, d349853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101145 (p : Pattern) (ha : d271214 p = 1) (hb : d309853 p = 1) : d349859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42578 q = 1) (hb : d271214 q = 1) : d349768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42578, d349768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101124 q ha hb
    | true =>
      simp only [d42578, d349768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101125 q ha hb
  have h2 (q : Pattern) (ha : d42579 q = 1) (hb : d271214 q = 1) : d349769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42579, d349769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42579, d349769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42580 q = 1) (hb : d271214 q = 1) : d349770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42580, d349770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42580, d349770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42581 q = 1) (hb : d271214 q = 1) : d349771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42581, d349771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42581, d349771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42588 q = 1) (hb : d271214 q = 1) : d349778 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42588, d349778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101126 q ha hb
    | true =>
      simp only [d42588, d349778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101127 q ha hb
  have h6 (q : Pattern) (ha : d42589 q = 1) (hb : d271214 q = 1) : d349779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42589, d349779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42589, d349779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42590 q = 1) (hb : d271214 q = 1) : d349780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42590, d349780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42590, d349780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42643 q = 1) (hb : d271214 q = 1) : d349827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42643, d349827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101136 q ha hb
    | true =>
      simp only [d42643, d349827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101112 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309844 q = 1) : d349828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309844, d349828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d309844, d349828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d42694 q = 1) (hb : d271214 q = 1) : d349833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42694, d349833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101137 q ha hb
    | true =>
      simp only [d42694, d349833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42695 q = 1) (hb : d271214 q = 1) : d349834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42695, d349834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42695, d349834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309845 q = 1) : d349835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309845, d349835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309845, d349835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309846 q = 1) : d349836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309846, d349836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309846, d349836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309847 q = 1) : d349837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309847, d349837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309847, d349837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42702 q = 1) (hb : d271214 q = 1) : d349841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42702, d349841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101139 q ha hb
    | true =>
      simp only [d42702, d349841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101140 q ha hb
  have h16 (q : Pattern) (ha : d42703 q = 1) (hb : d271214 q = 1) : d349842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42703, d349842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42703, d349842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42704 q = 1) (hb : d271214 q = 1) : d349843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42704, d349843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42704, d349843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42705 q = 1) (hb : d271214 q = 1) : d349844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42705, d349844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42705, d349844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42708 q = 1) (hb : d271214 q = 1) : d349847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42708, d349847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101141 q ha hb
    | true =>
      simp only [d42708, d349847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101142 q ha hb
  have h20 (q : Pattern) (ha : d42709 q = 1) (hb : d271214 q = 1) : d349848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42709, d349848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42709, d349848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d42710 q = 1) (hb : d271214 q = 1) : d349849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42710, d349849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42710, d349849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d42712 q = 1) (hb : d271214 q = 1) : d349851 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d349851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101143 q ha hb
    | true =>
      simp only [d42712, d349851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101115 q ha hb
  have h23 (q : Pattern) (ha : d271214 q = 1) (hb : d309849 q = 1) : d349852 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d349852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d309849, d349852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d42718 q = 1) (hb : d271214 q = 1) : d349854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d349854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101144 q ha hb
    | true =>
      simp only [d42718, d349854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d42719 q = 1) (hb : d271214 q = 1) : d349855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d349855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42719, d349855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d271214 q = 1) (hb : d309850 q = 1) : d349856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d349856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309850, d349856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d271214 q = 1) (hb : d309851 q = 1) : d349857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309851, d349857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d309851, d349857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d271214 q = 1) (hb : d309852 q = 1) : d349858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309852, d349858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d309852, d349858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d271214 q = 1) (hb : d309853 q = 1) : d349859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309853, d349859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309853, d349859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro101146 (p : Pattern) (ha : d271214 p = 1) (hb : d309860 p = 1) : d349879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42712 q = 1) (hb : d271214 q = 1) : d349851 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42712, d349851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101143 q ha hb
    | true =>
      simp only [d42712, d349851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101115 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309849 q = 1) : d349852 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309849, d349852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309849, d349852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d42718 q = 1) (hb : d271214 q = 1) : d349854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42718, d349854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101144 q ha hb
    | true =>
      simp only [d42718, d349854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42719 q = 1) (hb : d271214 q = 1) : d349855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42719, d349855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42719, d349855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309850 q = 1) : d349856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309850, d349856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309850, d349856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309858 q = 1) : d349877 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309858, d349877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309858, d349877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309859 q = 1) : d349878 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309859, d349878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309859, d349878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309860 q = 1) : d349879 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309860, d349879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309860, d349879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101147 (p : Pattern) (ha : d42765 p = 1) (hb : d271214 p = 1) : d349901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42751 q = 1) (hb : d271214 q = 1) : d349887 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42751, d349887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42751, d349887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101130 q ha hb
  have h2 (q : Pattern) (ha : d42608 q = 1) (hb : d271214 q = 1) : d349792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101130 q ha hb
    | true =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42752 q = 1) (hb : d271214 q = 1) : d349888 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42752, d349888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42752, d349888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42609 q = 1) (hb : d271214 q = 1) : d349793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42753 q = 1) (hb : d271214 q = 1) : d349889 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42753, d349889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42753, d349889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42754 q = 1) (hb : d271214 q = 1) : d349890 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42754, d349890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42754, d349890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42755 q = 1) (hb : d271214 q = 1) : d349891 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42755, d349891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42755, d349891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101131 q ha hb
  have h8 (q : Pattern) (ha : d42613 q = 1) (hb : d271214 q = 1) : d349797 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101131 q ha hb
    | true =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42756 q = 1) (hb : d271214 q = 1) : d349892 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42756, d349892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42756, d349892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42614 q = 1) (hb : d271214 q = 1) : d349798 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42757 q = 1) (hb : d271214 q = 1) : d349893 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42757, d349893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42757, d349893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42758 q = 1) (hb : d271214 q = 1) : d349894 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42758, d349894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42758, d349894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42759 q = 1) (hb : d271214 q = 1) : d349895 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42759, d349895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42759, d349895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42760 q = 1) (hb : d271214 q = 1) : d349896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
  have h15 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42761 q = 1) (hb : d271214 q = 1) : d349897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42762 q = 1) (hb : d271214 q = 1) : d349898 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42763 q = 1) (hb : d271214 q = 1) : d349899 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d42477 q = 1) (hb : d271214 q = 1) : d349686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d349686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42477, d349686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
  have h21 (q : Pattern) (ha : d42378 q = 1) (hb : d271214 q = 1) : d349618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
    | true =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d42478 q = 1) (hb : d271214 q = 1) : d349687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d349687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42478, d349687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d42379 q = 1) (hb : d271214 q = 1) : d349619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d42479 q = 1) (hb : d271214 q = 1) : d349688 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d349688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d42479, d349688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d42480 q = 1) (hb : d271214 q = 1) : d349689 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d349689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42480, d349689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d42764 q = 1) (hb : d271214 q = 1) : d349900 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42764, d349900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d42764, d349900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d42765 q = 1) (hb : d271214 q = 1) : d349901 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42765, d349901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42765, d349901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro101148 (p : Pattern) (ha : d42769 p = 1) (hb : d271214 p = 1) : d349905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42477 q = 1) (hb : d271214 q = 1) : d349686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42477, d349686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42477, d349686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
  have h2 (q : Pattern) (ha : d42378 q = 1) (hb : d271214 q = 1) : d349618 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101091 q ha hb
    | true =>
      simp only [d42378, d349618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42478 q = 1) (hb : d271214 q = 1) : d349687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42478, d349687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42478, d349687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42379 q = 1) (hb : d271214 q = 1) : d349619 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42379, d349619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42479 q = 1) (hb : d271214 q = 1) : d349688 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42479, d349688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42479, d349688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42480 q = 1) (hb : d271214 q = 1) : d349689 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42480, d349689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42480, d349689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d271214 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42481 q = 1) (hb : d271214 q = 1) : d349690 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42481, d349690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42481, d349690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d271214 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42769 q = 1) (hb : d271214 q = 1) : d349905 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42769, d349905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42769, d349905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro101149 (p : Pattern) (ha : d42775 p = 1) (hb : d271214 p = 1) : d349911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42766 q = 1) (hb : d271214 q = 1) : d349902 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42766, d349902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101147 q ha hb
    | true =>
      simp only [d42766, d349902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101103 q ha hb
  have h2 (q : Pattern) (ha : d42767 q = 1) (hb : d271214 q = 1) : d349903 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42767, d349903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42767, d349903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42768 q = 1) (hb : d271214 q = 1) : d349904 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42768, d349904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42768, d349904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42770 q = 1) (hb : d271214 q = 1) : d349906 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42770, d349906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101103 q ha hb
    | true =>
      simp only [d42770, d349906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101148 q ha hb
  have h5 (q : Pattern) (ha : d42771 q = 1) (hb : d271214 q = 1) : d349907 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42771, d349907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42771, d349907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42772 q = 1) (hb : d271214 q = 1) : d349908 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42772, d349908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42772, d349908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42773 q = 1) (hb : d271214 q = 1) : d349909 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42773, d349909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42773, d349909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42483 q = 1) (hb : d271214 q = 1) : d349692 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d349692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101103 q ha hb
    | true =>
      simp only [d42483, d349692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
  have h9 (q : Pattern) (ha : d42484 q = 1) (hb : d271214 q = 1) : d349693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d349693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42484, d349693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42485 q = 1) (hb : d271214 q = 1) : d349694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d349694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42485, d349694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d271214 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d42305 q = 1) (hb : d271214 q = 1) : d349547 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
    | true =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42306 q = 1) (hb : d271214 q = 1) : d349548 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42307 q = 1) (hb : d271214 q = 1) : d349549 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42486 q = 1) (hb : d271214 q = 1) : d349695 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d349695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42486, d349695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42774 q = 1) (hb : d271214 q = 1) : d349910 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42774, d349910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42774, d349910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42775 q = 1) (hb : d271214 q = 1) : d349911 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42775, d349911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42775, d349911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro101150 (p : Pattern) (ha : d42780 p = 1) (hb : d271214 p = 1) : d349916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42483 q = 1) (hb : d271214 q = 1) : d349692 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42483, d349692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101103 q ha hb
    | true =>
      simp only [d42483, d349692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
  have h2 (q : Pattern) (ha : d42484 q = 1) (hb : d271214 q = 1) : d349693 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42484, d349693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42484, d349693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42485 q = 1) (hb : d271214 q = 1) : d349694 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42485, d349694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42485, d349694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d271214 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42305 q = 1) (hb : d271214 q = 1) : d349547 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101079 q ha hb
    | true =>
      simp only [d42305, d349547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42306 q = 1) (hb : d271214 q = 1) : d349548 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42306, d349548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42307 q = 1) (hb : d271214 q = 1) : d349549 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42307, d349549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42486 q = 1) (hb : d271214 q = 1) : d349695 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42486, d349695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42486, d349695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42778 q = 1) (hb : d271214 q = 1) : d349914 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42778, d349914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42778, d349914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42779 q = 1) (hb : d271214 q = 1) : d349915 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42779, d349915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42779, d349915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42780 q = 1) (hb : d271214 q = 1) : d349916 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42780, d349916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42780, d349916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro101151 (p : Pattern) (ha : d42786 p = 1) (hb : d271214 p = 1) : d349922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42776 q = 1) (hb : d271214 q = 1) : d349912 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42776, d349912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101149 q ha hb
    | true =>
      simp only [d42776, d349912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42777 q = 1) (hb : d271214 q = 1) : d349913 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42777, d349913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42777, d349913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42781 q = 1) (hb : d271214 q = 1) : d349917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d349917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101150 q ha hb
    | true =>
      simp only [d42781, d349917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42782 q = 1) (hb : d271214 q = 1) : d349918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d349918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42782, d349918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42783 q = 1) (hb : d271214 q = 1) : d349919 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42783, d349919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42783, d349919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42784 q = 1) (hb : d271214 q = 1) : d349920 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42784, d349920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42784, d349920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42785 q = 1) (hb : d271214 q = 1) : d349921 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42785, d349921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42785, d349921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42786 q = 1) (hb : d271214 q = 1) : d349922 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42786, d349922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42786, d349922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101152 (p : Pattern) (ha : d42794 p = 1) (hb : d271214 p = 1) : d349930 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42781 q = 1) (hb : d271214 q = 1) : d349917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d349917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101150 q ha hb
    | true =>
      simp only [d42781, d349917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42782 q = 1) (hb : d271214 q = 1) : d349918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d349918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42782, d349918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42789 q = 1) (hb : d271214 q = 1) : d349925 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42789, d349925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101121 q ha hb
    | true =>
      simp only [d42789, d349925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42790 q = 1) (hb : d271214 q = 1) : d349926 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42790, d349926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42790, d349926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42791 q = 1) (hb : d271214 q = 1) : d349927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42791, d349927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42791, d349927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42792 q = 1) (hb : d271214 q = 1) : d349928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42792, d349928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42792, d349928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42793 q = 1) (hb : d271214 q = 1) : d349929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42793, d349929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42793, d349929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42794 q = 1) (hb : d271214 q = 1) : d349930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42794, d349930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42794, d349930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101153 (p : Pattern) (ha : d42833 p = 1) (hb : d271214 p = 1) : d349936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42781 q = 1) (hb : d271214 q = 1) : d349917 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42781, d349917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101150 q ha hb
    | true =>
      simp only [d42781, d349917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42782 q = 1) (hb : d271214 q = 1) : d349918 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42782, d349918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42782, d349918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42830 q = 1) (hb : d271214 q = 1) : d349933 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42830, d349933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42830, d349933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42831 q = 1) (hb : d271214 q = 1) : d349934 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42831, d349934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42831, d349934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42832 q = 1) (hb : d271214 q = 1) : d349935 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42832, d349935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42832, d349935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42833 q = 1) (hb : d271214 q = 1) : d349936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42833, d349936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42833, d349936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101154 (p : Pattern) (ha : d271214 p = 1) (hb : d309870 p = 1) : d349942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42795 q = 1) (hb : d271214 q = 1) : d349931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42795, d349931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101151 q ha hb
    | true =>
      simp only [d42795, d349931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101152 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309866 q = 1) : d349932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309866, d349932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309866, d349932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d42834 q = 1) (hb : d271214 q = 1) : d349937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42834, d349937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101153 q ha hb
    | true =>
      simp only [d42834, d349937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42835 q = 1) (hb : d271214 q = 1) : d349938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42835, d349938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42835, d349938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309867 q = 1) : d349939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309867, d349939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309867, d349939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309868 q = 1) : d349940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309868, d349940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309868, d349940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309869 q = 1) : d349941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309869, d349941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309869, d349941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309870 q = 1) : d349942 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309870, d349942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309870, d349942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101155 (p : Pattern) (ha : d271214 p = 1) (hb : d309876 p = 1) : d349959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42561 q = 1) (hb : d271214 q = 1) : d349751 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42561, d349751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42561, d349751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101114 q ha hb
  have h2 (q : Pattern) (ha : d42562 q = 1) (hb : d271214 q = 1) : d349752 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42562, d349752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42562, d349752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42571 q = 1) (hb : d271214 q = 1) : d349761 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42571, d349761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101114 q ha hb
    | true =>
      simp only [d42571, d349761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101117 q ha hb
  have h4 (q : Pattern) (ha : d42572 q = 1) (hb : d271214 q = 1) : d349762 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42572, d349762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42572, d349762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42573 q = 1) (hb : d271214 q = 1) : d349763 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42573, d349763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42573, d349763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309854 q = 1) : d349860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309854, d349860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101138 q ha hb
    | true =>
      simp only [d309854, d349860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101145 q ha hb
  have h7 (q : Pattern) (ha : d42737 q = 1) (hb : d271214 q = 1) : d349873 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42737, d349873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101118 q ha hb
    | true =>
      simp only [d42737, d349873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101119 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309855 q = 1) : d349874 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309855, d349874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309855, d349874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309856 q = 1) : d349875 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309856, d349875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309856, d349875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d271214 q = 1) (hb : d309857 q = 1) : d349876 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309857, d349876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d309857, d349876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309861 q = 1) : d349880 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309861, d349880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309861, d349880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101146 q ha hb
  have h12 (q : Pattern) (ha : d42746 q = 1) (hb : d271214 q = 1) : d349882 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42746, d349882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42746, d349882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101120 q ha hb
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309862 q = 1) : d349883 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309862, d349883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309862, d349883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309863 q = 1) : d349884 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309863, d349884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309863, d349884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309864 q = 1) : d349885 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309864, d349885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309864, d349885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309865 q = 1) : d349886 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309865, d349886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309865, d349886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271214 q = 1) (hb : d309871 q = 1) : d349943 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309871, d349943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309871, d349943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101154 q ha hb
  have h18 (q : Pattern) (ha : d42851 q = 1) (hb : d271214 q = 1) : d349954 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42851, d349954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42851, d349954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101123 q ha hb
  have h19 (q : Pattern) (ha : d271214 q = 1) (hb : d309872 q = 1) : d349955 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309872, d349955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309872, d349955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d271214 q = 1) (hb : d309873 q = 1) : d349956 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309873, d349956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309873, d349956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d271214 q = 1) (hb : d309874 q = 1) : d349957 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309874, d349957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309874, d349957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d271214 q = 1) (hb : d309875 q = 1) : d349958 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309875, d349958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309875, d349958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d271214 q = 1) (hb : d309876 q = 1) : d349959 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309876, d349959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309876, d349959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro101156 (p : Pattern) (ha : d271214 p = 1) (hb : d309882 p = 1) : d349965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d309877 q = 1) : d349960 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309877, d349960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309877, d349960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101155 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309878 q = 1) : d349961 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309878, d349961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309878, d349961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d309879 q = 1) : d349962 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309879, d349962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309879, d349962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d309880 q = 1) : d349963 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309880, d349963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309880, d349963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309881 q = 1) : d349964 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309881, d349964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309881, d349964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309882 q = 1) : d349965 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309882, d349965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309882, d349965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101157 (p : Pattern) (ha : d42864 p = 1) (hb : d271214 p = 1) : d349967 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21 q = 1) (hb : d271214 q = 1) : d21 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42253 q = 1) (hb : d271214 q = 1) : d349495 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42253, d349495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42253, d349495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42254 q = 1) (hb : d271214 q = 1) : d349496 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42254, d349496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42254, d349496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42864 q = 1) (hb : d271214 q = 1) : d349967 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42864, d349967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42864, d349967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101158 (p : Pattern) (ha : d42870 p = 1) (hb : d271214 p = 1) : d349973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42608 q = 1) (hb : d271214 q = 1) : d349792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101130 q ha hb
    | true =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42609 q = 1) (hb : d271214 q = 1) : d349793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42610 q = 1) (hb : d271214 q = 1) : d349794 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42610, d349794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42610, d349794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42611 q = 1) (hb : d271214 q = 1) : d349795 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42611, d349795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42611, d349795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42613 q = 1) (hb : d271214 q = 1) : d349797 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101131 q ha hb
    | true =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42614 q = 1) (hb : d271214 q = 1) : d349798 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42615 q = 1) (hb : d271214 q = 1) : d349799 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42615, d349799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42615, d349799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42616 q = 1) (hb : d271214 q = 1) : d349800 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42616, d349800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42616, d349800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42617 q = 1) (hb : d271214 q = 1) : d349801 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42617, d349801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42617, d349801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42623 q = 1) (hb : d271214 q = 1) : d349807 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42624 q = 1) (hb : d271214 q = 1) : d349808 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42867 q = 1) (hb : d271214 q = 1) : d349970 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42868 q = 1) (hb : d271214 q = 1) : d349971 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42869 q = 1) (hb : d271214 q = 1) : d349972 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42869, d349972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42869, d349972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42870 q = 1) (hb : d271214 q = 1) : d349973 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42870, d349973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42870, d349973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro101159 (p : Pattern) (ha : d42873 p = 1) (hb : d271214 p = 1) : d349976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42370 q = 1) (hb : d271214 q = 1) : d349610 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101090 q ha hb
    | true =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42371 q = 1) (hb : d271214 q = 1) : d349611 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42372 q = 1) (hb : d271214 q = 1) : d349612 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42372, d349612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42372, d349612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42373 q = 1) (hb : d271214 q = 1) : d349613 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42373, d349613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42373, d349613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42867 q = 1) (hb : d271214 q = 1) : d349970 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42868 q = 1) (hb : d271214 q = 1) : d349971 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42871 q = 1) (hb : d271214 q = 1) : d349974 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42871, d349974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42871, d349974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42872 q = 1) (hb : d271214 q = 1) : d349975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d349975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42872, d349975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42873 q = 1) (hb : d271214 q = 1) : d349976 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42873, d349976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42873, d349976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101160 (p : Pattern) (ha : d42877 p = 1) (hb : d271214 p = 1) : d349980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42867 q = 1) (hb : d271214 q = 1) : d349970 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42868 q = 1) (hb : d271214 q = 1) : d349971 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42872 q = 1) (hb : d271214 q = 1) : d349975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d349975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42872, d349975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42877 q = 1) (hb : d271214 q = 1) : d349980 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42877, d349980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42877, d349980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101161 (p : Pattern) (ha : d42884 p = 1) (hb : d271214 p = 1) : d349987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42874 q = 1) (hb : d271214 q = 1) : d349977 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42874, d349977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101158 q ha hb
    | true =>
      simp only [d42874, d349977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101159 q ha hb
  have h2 (q : Pattern) (ha : d42875 q = 1) (hb : d271214 q = 1) : d349978 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42875, d349978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42875, d349978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42876 q = 1) (hb : d271214 q = 1) : d349979 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42876, d349979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42876, d349979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42878 q = 1) (hb : d271214 q = 1) : d349981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d349981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101159 q ha hb
    | true =>
      simp only [d42878, d349981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101160 q ha hb
  have h5 (q : Pattern) (ha : d42879 q = 1) (hb : d271214 q = 1) : d349982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d349982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42879, d349982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42880 q = 1) (hb : d271214 q = 1) : d349983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d349983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42880, d349983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42881 q = 1) (hb : d271214 q = 1) : d349984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42881, d349984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42881, d349984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42882 q = 1) (hb : d271214 q = 1) : d349985 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d349985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42882, d349985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42883 q = 1) (hb : d271214 q = 1) : d349986 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42883, d349986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42883, d349986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42884 q = 1) (hb : d271214 q = 1) : d349987 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42884, d349987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42884, d349987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro101162 (p : Pattern) (ha : d42888 p = 1) (hb : d271214 p = 1) : d349991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42878 q = 1) (hb : d271214 q = 1) : d349981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d349981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101159 q ha hb
    | true =>
      simp only [d42878, d349981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101160 q ha hb
  have h2 (q : Pattern) (ha : d42879 q = 1) (hb : d271214 q = 1) : d349982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d349982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42879, d349982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42880 q = 1) (hb : d271214 q = 1) : d349983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d349983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42880, d349983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42882 q = 1) (hb : d271214 q = 1) : d349985 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42882, d349985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42882, d349985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42887 q = 1) (hb : d271214 q = 1) : d349990 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42887, d349990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42887, d349990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42888 q = 1) (hb : d271214 q = 1) : d349991 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42888, d349991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42888, d349991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101163 (p : Pattern) (ha : d42894 p = 1) (hb : d271214 p = 1) : d349997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d271214 q = 1) : d349994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d271214 q = 1) : d349995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42893 q = 1) (hb : d271214 q = 1) : d349996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d349996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d349996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42894 q = 1) (hb : d271214 q = 1) : d349997 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42894, d349997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42894, d349997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101164 (p : Pattern) (ha : d42898 p = 1) (hb : d271214 p = 1) : d350001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d271214 q = 1) : d349998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d271214 q = 1) : d349999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42897 q = 1) (hb : d271214 q = 1) : d350000 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d350000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d350000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42898 q = 1) (hb : d271214 q = 1) : d350001 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42898, d350001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42898, d350001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101165 (p : Pattern) (ha : d42904 p = 1) (hb : d271214 p = 1) : d350007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42899 q = 1) (hb : d271214 q = 1) : d350002 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101163 q ha hb
    | true =>
      simp only [d42899, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101164 q ha hb
  have h2 (q : Pattern) (ha : d42900 q = 1) (hb : d271214 q = 1) : d350003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42900, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42901 q = 1) (hb : d271214 q = 1) : d350004 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42902 q = 1) (hb : d271214 q = 1) : d350005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42902, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42903 q = 1) (hb : d271214 q = 1) : d350006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42903, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42904 q = 1) (hb : d271214 q = 1) : d350007 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42904, d350007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42904, d350007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101166 (p : Pattern) (ha : d42907 p = 1) (hb : d271214 p = 1) : d350010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d271214 q = 1) : d349994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d271214 q = 1) : d349995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42893 q = 1) (hb : d271214 q = 1) : d349996 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42893, d349996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42893, d349996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42907 q = 1) (hb : d271214 q = 1) : d350010 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42907, d350010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42907, d350010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101167 (p : Pattern) (ha : d42908 p = 1) (hb : d271214 p = 1) : d350011 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d271214 q = 1) : d349998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d271214 q = 1) : d349999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42897 q = 1) (hb : d271214 q = 1) : d350000 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42897, d350000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42897, d350000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42908 q = 1) (hb : d271214 q = 1) : d350011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42908, d350011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42908, d350011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101168 (p : Pattern) (ha : d42914 p = 1) (hb : d271214 p = 1) : d350017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42899 q = 1) (hb : d271214 q = 1) : d350002 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101163 q ha hb
    | true =>
      simp only [d42899, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101164 q ha hb
  have h2 (q : Pattern) (ha : d42900 q = 1) (hb : d271214 q = 1) : d350003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42900, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42901 q = 1) (hb : d271214 q = 1) : d350004 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42902 q = 1) (hb : d271214 q = 1) : d350005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42902, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42903 q = 1) (hb : d271214 q = 1) : d350006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42903, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42909 q = 1) (hb : d271214 q = 1) : d350012 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42909, d350012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101166 q ha hb
    | true =>
      simp only [d42909, d350012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101167 q ha hb
  have h7 (q : Pattern) (ha : d42910 q = 1) (hb : d271214 q = 1) : d350013 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42910, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42910, d350013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42911 q = 1) (hb : d271214 q = 1) : d350014 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42911, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42911, d350014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42912 q = 1) (hb : d271214 q = 1) : d350015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42912, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42912, d350015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42913 q = 1) (hb : d271214 q = 1) : d350016 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42913, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42913, d350016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42914 q = 1) (hb : d271214 q = 1) : d350017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d42914, d350017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42914, d350017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101169 (p : Pattern) (ha : d43111 p = 1) (hb : d271214 p = 1) : d350117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42899 q = 1) (hb : d271214 q = 1) : d350002 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42899, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101163 q ha hb
    | true =>
      simp only [d42899, d350002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101164 q ha hb
  have h2 (q : Pattern) (ha : d42900 q = 1) (hb : d271214 q = 1) : d350003 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42900, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42900, d350003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42901 q = 1) (hb : d271214 q = 1) : d350004 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42901, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42901, d350004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42902 q = 1) (hb : d271214 q = 1) : d350005 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42902, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42902, d350005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42903 q = 1) (hb : d271214 q = 1) : d350006 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d42903, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42903, d350006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43106 q = 1) (hb : d271214 q = 1) : d350112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d350112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101164 q ha hb
    | true =>
      simp only [d43106, d350112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43107 q = 1) (hb : d271214 q = 1) : d350113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d350113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43107, d350113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43108 q = 1) (hb : d271214 q = 1) : d350114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d350114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43108, d350114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43109 q = 1) (hb : d271214 q = 1) : d350115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d350115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43109, d350115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43110 q = 1) (hb : d271214 q = 1) : d350116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d350116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43110, d350116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43111 q = 1) (hb : d271214 q = 1) : d350117 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43111, d350117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43111, d350117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101170 (p : Pattern) (ha : d43117 p = 1) (hb : d271214 p = 1) : d350123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43106 q = 1) (hb : d271214 q = 1) : d350112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43106, d350112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101164 q ha hb
    | true =>
      simp only [d43106, d350112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43107 q = 1) (hb : d271214 q = 1) : d350113 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43107, d350113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43107, d350113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43108 q = 1) (hb : d271214 q = 1) : d350114 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43108, d350114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43108, d350114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43109 q = 1) (hb : d271214 q = 1) : d350115 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43109, d350115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43109, d350115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43110 q = 1) (hb : d271214 q = 1) : d350116 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43110, d350116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43110, d350116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43112 q = 1) (hb : d271214 q = 1) : d350118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d350118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101167 q ha hb
    | true =>
      simp only [d43112, d350118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43113 q = 1) (hb : d271214 q = 1) : d350119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d350119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43113, d350119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43114 q = 1) (hb : d271214 q = 1) : d350120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d350120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43114, d350120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43115 q = 1) (hb : d271214 q = 1) : d350121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d350121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43115, d350121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43116 q = 1) (hb : d271214 q = 1) : d350122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d350122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43116, d350122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43117 q = 1) (hb : d271214 q = 1) : d350123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43117, d350123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43117, d350123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101171 (p : Pattern) (ha : d43126 p = 1) (hb : d271214 p = 1) : d350132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43112 q = 1) (hb : d271214 q = 1) : d350118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43112, d350118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101167 q ha hb
    | true =>
      simp only [d43112, d350118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43113 q = 1) (hb : d271214 q = 1) : d350119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43113, d350119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43113, d350119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43114 q = 1) (hb : d271214 q = 1) : d350120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43114, d350120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43114, d350120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43115 q = 1) (hb : d271214 q = 1) : d350121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43115, d350121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43115, d350121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43116 q = 1) (hb : d271214 q = 1) : d350122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43116, d350122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43116, d350122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43126 q = 1) (hb : d271214 q = 1) : d350132 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43126, d350132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43126, d350132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101172 (p : Pattern) (ha : d43163 p = 1) (hb : d271214 p = 1) : d350169 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42472 q = 1) (hb : d271214 q = 1) : d349681 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42472, d349681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42472, d349681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101090 q ha hb
  have h2 (q : Pattern) (ha : d42370 q = 1) (hb : d271214 q = 1) : d349610 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101090 q ha hb
    | true =>
      simp only [d42370, d349610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42473 q = 1) (hb : d271214 q = 1) : d349682 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42473, d349682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42473, d349682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42371 q = 1) (hb : d271214 q = 1) : d349611 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42371, d349611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42474 q = 1) (hb : d271214 q = 1) : d349683 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42474, d349683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42474, d349683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42475 q = 1) (hb : d271214 q = 1) : d349684 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42475, d349684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42475, d349684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43147 q = 1) (hb : d271214 q = 1) : d350153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
  have h8 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43148 q = 1) (hb : d271214 q = 1) : d350154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43149 q = 1) (hb : d271214 q = 1) : d350155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43150 q = 1) (hb : d271214 q = 1) : d350156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43162 q = 1) (hb : d271214 q = 1) : d350168 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43162, d350168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43162, d350168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43156 q = 1) (hb : d271214 q = 1) : d350162 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d350162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43156, d350162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43163 q = 1) (hb : d271214 q = 1) : d350169 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43163, d350169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43163, d350169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101173 (p : Pattern) (ha : d43167 p = 1) (hb : d271214 p = 1) : d350173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43147 q = 1) (hb : d271214 q = 1) : d350153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
  have h2 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43148 q = 1) (hb : d271214 q = 1) : d350154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43149 q = 1) (hb : d271214 q = 1) : d350155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43150 q = 1) (hb : d271214 q = 1) : d350156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43156 q = 1) (hb : d271214 q = 1) : d350162 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d350162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43156, d350162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43167 q = 1) (hb : d271214 q = 1) : d350173 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43167, d350173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43167, d350173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101174 (p : Pattern) (ha : d43186 p = 1) (hb : d271214 p = 1) : d350192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43168 q = 1) (hb : d271214 q = 1) : d350174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d350174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101172 q ha hb
    | true =>
      simp only [d43168, d350174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101173 q ha hb
  have h2 (q : Pattern) (ha : d43169 q = 1) (hb : d271214 q = 1) : d350175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d350175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43169, d350175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43170 q = 1) (hb : d271214 q = 1) : d350176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d350176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43170, d350176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43176 q = 1) (hb : d271214 q = 1) : d350182 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43176, d350182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43176, d350182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43185 q = 1) (hb : d271214 q = 1) : d350191 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43185, d350191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43185, d350191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43186 q = 1) (hb : d271214 q = 1) : d350192 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43186, d350192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43186, d350192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101175 (p : Pattern) (ha : d43257 p = 1) (hb : d271214 p = 1) : d350215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43187 q = 1) (hb : d271214 q = 1) : d350193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43187, d350193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101174 q ha hb
    | true =>
      simp only [d43187, d350193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43188 q = 1) (hb : d271214 q = 1) : d350194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43188, d350194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43188, d350194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43254 q = 1) (hb : d271214 q = 1) : d350212 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43254, d350212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43254, d350212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43255 q = 1) (hb : d271214 q = 1) : d350213 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43255, d350213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43255, d350213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43256 q = 1) (hb : d271214 q = 1) : d350214 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43256, d350214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43256, d350214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43257 q = 1) (hb : d271214 q = 1) : d350215 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43257, d350215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43257, d350215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101176 (p : Pattern) (ha : d43263 p = 1) (hb : d271214 p = 1) : d350221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43258 q = 1) (hb : d271214 q = 1) : d350216 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43258, d350216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101175 q ha hb
    | true =>
      simp only [d43258, d350216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43259 q = 1) (hb : d271214 q = 1) : d350217 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43259, d350217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43259, d350217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43260 q = 1) (hb : d271214 q = 1) : d350218 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43260, d350218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43260, d350218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43261 q = 1) (hb : d271214 q = 1) : d350219 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43261, d350219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43261, d350219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43262 q = 1) (hb : d271214 q = 1) : d350220 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43262, d350220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43262, d350220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43263 q = 1) (hb : d271214 q = 1) : d350221 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43263, d350221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43263, d350221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101177 (p : Pattern) (ha : d42919 p = 1) (hb : d271214 p = 1) : d350022 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d271214 q = 1) : d349994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d271214 q = 1) : d349995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42918 q = 1) (hb : d271214 q = 1) : d350021 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42918, d350021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42918, d350021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42919 q = 1) (hb : d271214 q = 1) : d350022 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42919, d350022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42919, d350022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101178 (p : Pattern) (ha : d42921 p = 1) (hb : d271214 p = 1) : d350024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d271214 q = 1) : d349998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d271214 q = 1) : d349999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42920 q = 1) (hb : d271214 q = 1) : d350023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42920, d350023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42920, d350023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42921 q = 1) (hb : d271214 q = 1) : d350024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42921, d350024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42921, d350024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101179 (p : Pattern) (ha : d42928 p = 1) (hb : d271214 p = 1) : d350031 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d271214 q = 1) : d349994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42926 q = 1) (hb : d271214 q = 1) : d350029 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42926, d350029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42926, d350029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42927 q = 1) (hb : d271214 q = 1) : d350030 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42927, d350030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42927, d350030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42928 q = 1) (hb : d271214 q = 1) : d350031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42928, d350031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42928, d350031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101180 (p : Pattern) (ha : d42931 p = 1) (hb : d271214 p = 1) : d350034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d271214 q = 1) : d349998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42929 q = 1) (hb : d271214 q = 1) : d350032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42929, d350032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42929, d350032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42930 q = 1) (hb : d271214 q = 1) : d350033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42930, d350033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42930, d350033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42931 q = 1) (hb : d271214 q = 1) : d350034 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42931, d350034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42931, d350034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101181 (p : Pattern) (ha : d42941 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2002 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2005 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1084 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1085 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42940 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42941 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101182 (p : Pattern) (ha : d42945 p = 1) (hb : d271214 p = 1) : d349785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d1519 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d42592 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42592, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42592, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d42246 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d42598 q = 1) (hb : d271214 q = 1) : d1531 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42598, d1531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42944 q = 1) (hb : d271214 q = 1) : d43873 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42944, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42944, d43873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16 q = 1) (hb : d271214 q = 1) : d16 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d42600 q = 1) (hb : d271214 q = 1) : d9579 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42600, d9579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42600, d9579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42945 q = 1) (hb : d271214 q = 1) : d349785 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42945, d349785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42945, d349785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro101183 (p : Pattern) (ha : d42954 p = 1) (hb : d271214 p = 1) : d350042 p = 1 := by
  have h0 (q : Pattern) (ha : d42938 q = 1) (hb : d271214 q = 1) : d42938 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42595 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42596 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d42939 q = 1) (hb : d271214 q = 1) : d350038 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42939, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42939, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42942 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101181 q ha hb
    | true =>
      simp only [d42942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d42943 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d42946 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101182 q ha hb
    | true =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d42947 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d42948 q = 1) (hb : d271214 q = 1) : d350039 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42948, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42949 q = 1) (hb : d271214 q = 1) : d350040 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42949, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42949, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42950 q = 1) (hb : d271214 q = 1) : d350041 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42950, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42950, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d42364 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d42365 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d42597 q = 1) (hb : d271214 q = 1) : d349784 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42597, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d42951 q = 1) (hb : d271214 q = 1) : d349788 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42951, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42951, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d42952 q = 1) (hb : d271214 q = 1) : d349789 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42952, d349789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42952, d349789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42953 q = 1) (hb : d271214 q = 1) : d349790 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42953, d349790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42953, d349790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h20 (q : Pattern) (ha : d42954 q = 1) (hb : d271214 q = 1) : d350042 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42954, d350042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42954, d350042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro101184 (p : Pattern) (ha : d42961 p = 1) (hb : d271214 p = 1) : d349603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d271213 q = 1) : d308 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d42246 q = 1) (hb : d271214 q = 1) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42246, d271214, d1519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d42361 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d42361, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42361, d34366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1540 q = 1) (hb : d271214 q = 1) : d1540 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d42959 q = 1) (hb : d271214 q = 1) : d43420 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42959, d43420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42959, d43420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d42960 q = 1) (hb : d271214 q = 1) : d42960 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42961 q = 1) (hb : d271214 q = 1) : d349603 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d42961, d349603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42961, d349603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro101185 (p : Pattern) (ha : d42967 p = 1) (hb : d271214 p = 1) : d350047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42595 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42596 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42364 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d42364, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42365 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42365, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42597 q = 1) (hb : d271214 q = 1) : d349784 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42597, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42597, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42602 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101129 q ha hb
    | true =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42603 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42604 q = 1) (hb : d271214 q = 1) : d349788 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42605 q = 1) (hb : d271214 q = 1) : d349789 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42605, d349789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42605, d349789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42606 q = 1) (hb : d271214 q = 1) : d349790 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42606, d349790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42606, d349790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42962 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101184 q ha hb
    | true =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42963 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42964 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42964, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42964, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d42965 q = 1) (hb : d271214 q = 1) : d349802 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42965, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42965, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d42966 q = 1) (hb : d271214 q = 1) : d349803 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42966, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42966, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42967 q = 1) (hb : d271214 q = 1) : d350047 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42967, d350047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42967, d350047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro101186 (p : Pattern) (ha : d42976 p = 1) (hb : d271214 p = 1) : d350055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42595 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d42595, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42596 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42596, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42962 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101184 q ha hb
    | true =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42963 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42973 q = 1) (hb : d271214 q = 1) : d349784 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42973, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42973, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42974 q = 1) (hb : d271214 q = 1) : d350053 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42974, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42974, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42975 q = 1) (hb : d271214 q = 1) : d350054 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42975, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42975, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d42964 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42964, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42964, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42965 q = 1) (hb : d271214 q = 1) : d349802 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d42965, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42965, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42966 q = 1) (hb : d271214 q = 1) : d349803 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d42966, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42966, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42976 q = 1) (hb : d271214 q = 1) : d350055 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d42976, d350055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42976, d350055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro101187 (p : Pattern) (ha : d42982 p = 1) (hb : d271214 p = 1) : d350061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42955 q = 1) (hb : d271214 q = 1) : d350043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42955, d350043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101183 q ha hb
    | true =>
      simp only [d42955, d350043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42956 q = 1) (hb : d271214 q = 1) : d350044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42956, d350044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42956, d350044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42957 q = 1) (hb : d271214 q = 1) : d350045 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42957, d350045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42957, d350045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42958 q = 1) (hb : d271214 q = 1) : d350046 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42958, d350046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42958, d350046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42968 q = 1) (hb : d271214 q = 1) : d350048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42968, d350048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101185 q ha hb
    | true =>
      simp only [d42968, d350048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42969 q = 1) (hb : d271214 q = 1) : d350049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42969, d350049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42969, d350049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42970 q = 1) (hb : d271214 q = 1) : d350050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42970, d350050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42970, d350050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42971 q = 1) (hb : d271214 q = 1) : d350051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42971, d350051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42971, d350051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42972 q = 1) (hb : d271214 q = 1) : d350052 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42972, d350052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42972, d350052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42977 q = 1) (hb : d271214 q = 1) : d350056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42977, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101186 q ha hb
    | true =>
      simp only [d42977, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42978 q = 1) (hb : d271214 q = 1) : d350057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42978, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42978, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d42979 q = 1) (hb : d271214 q = 1) : d350058 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42979, d350058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42979, d350058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42980 q = 1) (hb : d271214 q = 1) : d350059 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42980, d350059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d42980, d350059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42623 q = 1) (hb : d271214 q = 1) : d349807 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42624 q = 1) (hb : d271214 q = 1) : d349808 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42981 q = 1) (hb : d271214 q = 1) : d350060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42981, d350060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d42981, d350060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42982 q = 1) (hb : d271214 q = 1) : d350061 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42982, d350061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42982, d350061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro101188 (p : Pattern) (ha : d42986 p = 1) (hb : d271214 p = 1) : d350065 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42623 q = 1) (hb : d271214 q = 1) : d349807 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42623, d349807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42624 q = 1) (hb : d271214 q = 1) : d349808 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42624, d349808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42867 q = 1) (hb : d271214 q = 1) : d349970 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42867, d349970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42868 q = 1) (hb : d271214 q = 1) : d349971 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42868, d349971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42869 q = 1) (hb : d271214 q = 1) : d349972 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42869, d349972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42869, d349972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42872 q = 1) (hb : d271214 q = 1) : d349975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42872, d349975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42872, d349975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42986 q = 1) (hb : d271214 q = 1) : d350065 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d42986, d350065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42986, d350065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101189 (p : Pattern) (ha : d42992 p = 1) (hb : d271214 p = 1) : d350071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42983 q = 1) (hb : d271214 q = 1) : d350062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42983, d350062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101187 q ha hb
    | true =>
      simp only [d42983, d350062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101158 q ha hb
  have h2 (q : Pattern) (ha : d42984 q = 1) (hb : d271214 q = 1) : d350063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42984, d350063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42984, d350063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42985 q = 1) (hb : d271214 q = 1) : d350064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42985, d350064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42985, d350064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42987 q = 1) (hb : d271214 q = 1) : d350066 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42987, d350066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101158 q ha hb
    | true =>
      simp only [d42987, d350066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101188 q ha hb
  have h5 (q : Pattern) (ha : d42988 q = 1) (hb : d271214 q = 1) : d350067 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42988, d350067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42988, d350067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42989 q = 1) (hb : d271214 q = 1) : d350068 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42989, d350068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42989, d350068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42990 q = 1) (hb : d271214 q = 1) : d350069 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42990, d350069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42990, d350069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d42874 q = 1) (hb : d271214 q = 1) : d349977 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42874, d349977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101158 q ha hb
    | true =>
      simp only [d42874, d349977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101159 q ha hb
  have h9 (q : Pattern) (ha : d42875 q = 1) (hb : d271214 q = 1) : d349978 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42875, d349978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42875, d349978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42876 q = 1) (hb : d271214 q = 1) : d349979 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42876, d349979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42876, d349979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42878 q = 1) (hb : d271214 q = 1) : d349981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d42878, d349981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101159 q ha hb
    | true =>
      simp only [d42878, d349981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101160 q ha hb
  have h12 (q : Pattern) (ha : d42879 q = 1) (hb : d271214 q = 1) : d349982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d42879, d349982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42879, d349982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d42880 q = 1) (hb : d271214 q = 1) : d349983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d42880, d349983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42880, d349983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42881 q = 1) (hb : d271214 q = 1) : d349984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d42881, d349984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42881, d349984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42991 q = 1) (hb : d271214 q = 1) : d350070 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d42991, d350070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42991, d350070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d42992 q = 1) (hb : d271214 q = 1) : d350071 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d42992, d350071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42992, d350071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro101190 (p : Pattern) (ha : d42998 p = 1) (hb : d271214 p = 1) : d350077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42993 q = 1) (hb : d271214 q = 1) : d350072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42993, d350072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101189 q ha hb
    | true =>
      simp only [d42993, d350072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42994 q = 1) (hb : d271214 q = 1) : d350073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42994, d350073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42994, d350073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42995 q = 1) (hb : d271214 q = 1) : d350074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42995, d350074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42995, d350074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42996 q = 1) (hb : d271214 q = 1) : d350075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42996, d350075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42996, d350075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42997 q = 1) (hb : d271214 q = 1) : d350076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42997, d350076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42997, d350076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42998 q = 1) (hb : d271214 q = 1) : d350077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d42998, d350077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42998, d350077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101191 (p : Pattern) (ha : d43074 p = 1) (hb : d271214 p = 1) : d350083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43071 q = 1) (hb : d271214 q = 1) : d350080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43071, d350080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43071, d350080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43072 q = 1) (hb : d271214 q = 1) : d350081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43072, d350081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43072, d350081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43073 q = 1) (hb : d271214 q = 1) : d350082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43073, d350082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43073, d350082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43074 q = 1) (hb : d271214 q = 1) : d350083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43074, d350083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43074, d350083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101192 (p : Pattern) (ha : d271214 p = 1) (hb : d309888 p = 1) : d350089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42922 q = 1) (hb : d271214 q = 1) : d350025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42922, d350025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101177 q ha hb
    | true =>
      simp only [d42922, d350025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101178 q ha hb
  have h2 (q : Pattern) (ha : d42923 q = 1) (hb : d271214 q = 1) : d350026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42923, d350026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42923, d350026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42924 q = 1) (hb : d271214 q = 1) : d350027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42924, d350027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42924, d350027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42925 q = 1) (hb : d271214 q = 1) : d350028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42925, d350028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42925, d350028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42932 q = 1) (hb : d271214 q = 1) : d350035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42932, d350035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101179 q ha hb
    | true =>
      simp only [d42932, d350035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101180 q ha hb
  have h6 (q : Pattern) (ha : d42933 q = 1) (hb : d271214 q = 1) : d350036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42933, d350036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42933, d350036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42934 q = 1) (hb : d271214 q = 1) : d350037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42934, d350037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42934, d350037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42999 q = 1) (hb : d271214 q = 1) : d350078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42999, d350078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101190 q ha hb
    | true =>
      simp only [d42999, d350078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101163 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309884 q = 1) : d350079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d350079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d309884, d350079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43075 q = 1) (hb : d271214 q = 1) : d350084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43075, d350084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101191 q ha hb
    | true =>
      simp only [d43075, d350084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43076 q = 1) (hb : d271214 q = 1) : d350085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43076, d350085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43076, d350085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309885 q = 1) : d350086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d350086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309885, d350086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309886 q = 1) : d350087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d350087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309886, d350087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309887 q = 1) : d350088 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d350088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309887, d350088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309888 q = 1) : d350089 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309888, d350089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309888, d350089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101193 (p : Pattern) (ha : d43081 p = 1) (hb : d271214 p = 1) : d350090 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d271214 q = 1) : d349994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42892 q = 1) (hb : d271214 q = 1) : d349995 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42892, d349995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42918 q = 1) (hb : d271214 q = 1) : d350021 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42918, d350021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42918, d350021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43081 q = 1) (hb : d271214 q = 1) : d350090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43081, d350090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43081, d350090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101194 (p : Pattern) (ha : d43082 p = 1) (hb : d271214 p = 1) : d350091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d271214 q = 1) : d349998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42896 q = 1) (hb : d271214 q = 1) : d349999 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42896, d349999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42920 q = 1) (hb : d271214 q = 1) : d350023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42920, d350023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42920, d350023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43082 q = 1) (hb : d271214 q = 1) : d350091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43082, d350091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43082, d350091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101195 (p : Pattern) (ha : d43087 p = 1) (hb : d271214 p = 1) : d350096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42891 q = 1) (hb : d271214 q = 1) : d349994 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42891, d349994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42926 q = 1) (hb : d271214 q = 1) : d350029 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42926, d350029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42926, d350029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42927 q = 1) (hb : d271214 q = 1) : d350030 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42927, d350030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42927, d350030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43087 q = 1) (hb : d271214 q = 1) : d350096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43087, d350096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43087, d350096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101196 (p : Pattern) (ha : d43088 p = 1) (hb : d271214 p = 1) : d350097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42889 q = 1) (hb : d271214 q = 1) : d349992 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101162 q ha hb
    | true =>
      simp only [d42889, d349992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42890 q = 1) (hb : d271214 q = 1) : d349993 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42890, d349993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42895 q = 1) (hb : d271214 q = 1) : d349998 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42895, d349998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42929 q = 1) (hb : d271214 q = 1) : d350032 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42929, d350032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42929, d350032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42930 q = 1) (hb : d271214 q = 1) : d350033 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42930, d350033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42930, d350033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43088 q = 1) (hb : d271214 q = 1) : d350097 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43088, d350097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43088, d350097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101197 (p : Pattern) (ha : d43092 p = 1) (hb : d271214 p = 1) : d350101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42993 q = 1) (hb : d271214 q = 1) : d350072 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42993, d350072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101189 q ha hb
    | true =>
      simp only [d42993, d350072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42994 q = 1) (hb : d271214 q = 1) : d350073 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42994, d350073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42994, d350073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42995 q = 1) (hb : d271214 q = 1) : d350074 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d42995, d350074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42995, d350074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42996 q = 1) (hb : d271214 q = 1) : d350075 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d42996, d350075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42996, d350075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42997 q = 1) (hb : d271214 q = 1) : d350076 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d42997, d350076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42997, d350076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43092 q = 1) (hb : d271214 q = 1) : d350101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43092, d350101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43092, d350101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101198 (p : Pattern) (ha : d43098 p = 1) (hb : d271214 p = 1) : d350104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42885 q = 1) (hb : d271214 q = 1) : d349988 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101161 q ha hb
    | true =>
      simp only [d42885, d349988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d42886 q = 1) (hb : d271214 q = 1) : d349989 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42886, d349989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43071 q = 1) (hb : d271214 q = 1) : d350080 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43071, d350080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43071, d350080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43072 q = 1) (hb : d271214 q = 1) : d350081 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43072, d350081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43072, d350081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43073 q = 1) (hb : d271214 q = 1) : d350082 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43073, d350082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43073, d350082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43098 q = 1) (hb : d271214 q = 1) : d350104 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43098, d350104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43098, d350104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101199 (p : Pattern) (ha : d271214 p = 1) (hb : d309893 p = 1) : d350110 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42922 q = 1) (hb : d271214 q = 1) : d350025 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42922, d350025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101177 q ha hb
    | true =>
      simp only [d42922, d350025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101178 q ha hb
  have h2 (q : Pattern) (ha : d42923 q = 1) (hb : d271214 q = 1) : d350026 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42923, d350026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42923, d350026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42924 q = 1) (hb : d271214 q = 1) : d350027 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42924, d350027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42924, d350027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d42925 q = 1) (hb : d271214 q = 1) : d350028 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d42925, d350028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42925, d350028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42932 q = 1) (hb : d271214 q = 1) : d350035 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42932, d350035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101179 q ha hb
    | true =>
      simp only [d42932, d350035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101180 q ha hb
  have h6 (q : Pattern) (ha : d42933 q = 1) (hb : d271214 q = 1) : d350036 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d42933, d350036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42933, d350036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42934 q = 1) (hb : d271214 q = 1) : d350037 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d42934, d350037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42934, d350037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42999 q = 1) (hb : d271214 q = 1) : d350078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d42999, d350078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101190 q ha hb
    | true =>
      simp only [d42999, d350078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101163 q ha hb
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309884 q = 1) : d350079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309884, d350079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d309884, d350079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43075 q = 1) (hb : d271214 q = 1) : d350084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43075, d350084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101191 q ha hb
    | true =>
      simp only [d43075, d350084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43076 q = 1) (hb : d271214 q = 1) : d350085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43076, d350085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43076, d350085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d271214 q = 1) (hb : d309885 q = 1) : d350086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309885, d350086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d309885, d350086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309886 q = 1) : d350087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309886, d350087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d309886, d350087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309887 q = 1) : d350088 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309887, d350088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d309887, d350088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43083 q = 1) (hb : d271214 q = 1) : d350092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43083, d350092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101193 q ha hb
    | true =>
      simp only [d43083, d350092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101194 q ha hb
  have h16 (q : Pattern) (ha : d43084 q = 1) (hb : d271214 q = 1) : d350093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43084, d350093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43084, d350093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43085 q = 1) (hb : d271214 q = 1) : d350094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43085, d350094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43085, d350094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43086 q = 1) (hb : d271214 q = 1) : d350095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43086, d350095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43086, d350095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43089 q = 1) (hb : d271214 q = 1) : d350098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43089, d350098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101195 q ha hb
    | true =>
      simp only [d43089, d350098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101196 q ha hb
  have h20 (q : Pattern) (ha : d43090 q = 1) (hb : d271214 q = 1) : d350099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43090, d350099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43090, d350099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d43091 q = 1) (hb : d271214 q = 1) : d350100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43091, d350100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43091, d350100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d43093 q = 1) (hb : d271214 q = 1) : d350102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43093, d350102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101197 q ha hb
    | true =>
      simp only [d43093, d350102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101166 q ha hb
  have h23 (q : Pattern) (ha : d271214 q = 1) (hb : d309889 q = 1) : d350103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d350103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d309889, d350103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d43099 q = 1) (hb : d271214 q = 1) : d350105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43099, d350105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101198 q ha hb
    | true =>
      simp only [d43099, d350105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d43100 q = 1) (hb : d271214 q = 1) : d350106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43100, d350106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43100, d350106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d271214 q = 1) (hb : d309890 q = 1) : d350107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d350107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d309890, d350107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d271214 q = 1) (hb : d309891 q = 1) : d350108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309891, d350108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d309891, d350108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d271214 q = 1) (hb : d309892 q = 1) : d350109 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309892, d350109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d309892, d350109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d271214 q = 1) (hb : d309893 q = 1) : d350110 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309893, d350110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309893, d350110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro101200 (p : Pattern) (ha : d271214 p = 1) (hb : d309900 p = 1) : d350130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43093 q = 1) (hb : d271214 q = 1) : d350102 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43093, d350102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101197 q ha hb
    | true =>
      simp only [d43093, d350102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101166 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309889 q = 1) : d350103 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309889, d350103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309889, d350103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d43099 q = 1) (hb : d271214 q = 1) : d350105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43099, d350105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101198 q ha hb
    | true =>
      simp only [d43099, d350105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43100 q = 1) (hb : d271214 q = 1) : d350106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43100, d350106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43100, d350106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309890 q = 1) : d350107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309890, d350107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309890, d350107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309898 q = 1) : d350128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309898, d350128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309898, d350128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309899 q = 1) : d350129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309899, d350129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309899, d350129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309900 q = 1) : d350130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309900, d350130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309900, d350130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101201 (p : Pattern) (ha : d43146 p = 1) (hb : d271214 p = 1) : d350152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43132 q = 1) (hb : d271214 q = 1) : d350138 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43132, d350138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43132, d350138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101183 q ha hb
  have h2 (q : Pattern) (ha : d42955 q = 1) (hb : d271214 q = 1) : d350043 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42955, d350043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101183 q ha hb
    | true =>
      simp only [d42955, d350043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43133 q = 1) (hb : d271214 q = 1) : d350139 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43133, d350139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43133, d350139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42956 q = 1) (hb : d271214 q = 1) : d350044 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42956, d350044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42956, d350044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43134 q = 1) (hb : d271214 q = 1) : d350140 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43134, d350140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43134, d350140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43135 q = 1) (hb : d271214 q = 1) : d350141 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43135, d350141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43135, d350141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43136 q = 1) (hb : d271214 q = 1) : d350142 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43136, d350142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43136, d350142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101185 q ha hb
  have h8 (q : Pattern) (ha : d42968 q = 1) (hb : d271214 q = 1) : d350048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42968, d350048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101185 q ha hb
    | true =>
      simp only [d42968, d350048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43137 q = 1) (hb : d271214 q = 1) : d350143 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43137, d350143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43137, d350143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42969 q = 1) (hb : d271214 q = 1) : d350049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42969, d350049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42969, d350049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43138 q = 1) (hb : d271214 q = 1) : d350144 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43138, d350144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43138, d350144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43139 q = 1) (hb : d271214 q = 1) : d350145 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43139, d350145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43139, d350145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43140 q = 1) (hb : d271214 q = 1) : d350146 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43140, d350146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43140, d350146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43141 q = 1) (hb : d271214 q = 1) : d350147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43141, d350147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43141, d350147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101186 q ha hb
  have h15 (q : Pattern) (ha : d42977 q = 1) (hb : d271214 q = 1) : d350056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42977, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101186 q ha hb
    | true =>
      simp only [d42977, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43142 q = 1) (hb : d271214 q = 1) : d350148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43142, d350148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43142, d350148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42978 q = 1) (hb : d271214 q = 1) : d350057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42978, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42978, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43143 q = 1) (hb : d271214 q = 1) : d350149 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43143, d350149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43143, d350149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43144 q = 1) (hb : d271214 q = 1) : d350150 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43144, d350150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43144, d350150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d42760 q = 1) (hb : d271214 q = 1) : d349896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
  have h21 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d42761 q = 1) (hb : d271214 q = 1) : d349897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d42762 q = 1) (hb : d271214 q = 1) : d349898 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d42763 q = 1) (hb : d271214 q = 1) : d349899 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d43145 q = 1) (hb : d271214 q = 1) : d350151 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43145, d350151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43145, d350151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d43146 q = 1) (hb : d271214 q = 1) : d350152 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43146, d350152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43146, d350152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro101202 (p : Pattern) (ha : d43152 p = 1) (hb : d271214 p = 1) : d350158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42751 q = 1) (hb : d271214 q = 1) : d349887 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42751, d349887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42751, d349887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101130 q ha hb
  have h2 (q : Pattern) (ha : d42608 q = 1) (hb : d271214 q = 1) : d349792 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101130 q ha hb
    | true =>
      simp only [d42608, d349792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42752 q = 1) (hb : d271214 q = 1) : d349888 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42752, d349888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42752, d349888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42609 q = 1) (hb : d271214 q = 1) : d349793 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42609, d349793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42753 q = 1) (hb : d271214 q = 1) : d349889 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42753, d349889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42753, d349889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42754 q = 1) (hb : d271214 q = 1) : d349890 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42754, d349890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42754, d349890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d42755 q = 1) (hb : d271214 q = 1) : d349891 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42755, d349891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42755, d349891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101131 q ha hb
  have h8 (q : Pattern) (ha : d42613 q = 1) (hb : d271214 q = 1) : d349797 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101131 q ha hb
    | true =>
      simp only [d42613, d349797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d42756 q = 1) (hb : d271214 q = 1) : d349892 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42756, d349892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42756, d349892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42614 q = 1) (hb : d271214 q = 1) : d349798 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42614, d349798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d42757 q = 1) (hb : d271214 q = 1) : d349893 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42757, d349893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42757, d349893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d42758 q = 1) (hb : d271214 q = 1) : d349894 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42758, d349894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42758, d349894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d42759 q = 1) (hb : d271214 q = 1) : d349895 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d42759, d349895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42759, d349895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d42760 q = 1) (hb : d271214 q = 1) : d349896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
  have h15 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d42761 q = 1) (hb : d271214 q = 1) : d349897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d42762 q = 1) (hb : d271214 q = 1) : d349898 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d42763 q = 1) (hb : d271214 q = 1) : d349899 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d43147 q = 1) (hb : d271214 q = 1) : d350153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
  have h21 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d43148 q = 1) (hb : d271214 q = 1) : d350154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d43149 q = 1) (hb : d271214 q = 1) : d350155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d43150 q = 1) (hb : d271214 q = 1) : d350156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d43151 q = 1) (hb : d271214 q = 1) : d350157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43151, d350157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43151, d350157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d43152 q = 1) (hb : d271214 q = 1) : d350158 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43152, d350158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43152, d350158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro101203 (p : Pattern) (ha : d43157 p = 1) (hb : d271214 p = 1) : d350163 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42760 q = 1) (hb : d271214 q = 1) : d349896 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42760, d349896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
  have h2 (q : Pattern) (ha : d42621 q = 1) (hb : d271214 q = 1) : d349805 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101132 q ha hb
    | true =>
      simp only [d42621, d349805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42761 q = 1) (hb : d271214 q = 1) : d349897 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42761, d349897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d42622 q = 1) (hb : d271214 q = 1) : d349806 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42622, d349806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42762 q = 1) (hb : d271214 q = 1) : d349898 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42762, d349898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42763 q = 1) (hb : d271214 q = 1) : d349899 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42763, d349899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43147 q = 1) (hb : d271214 q = 1) : d350153 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43147, d350153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
  have h8 (q : Pattern) (ha : d42865 q = 1) (hb : d271214 q = 1) : d349968 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101157 q ha hb
    | true =>
      simp only [d42865, d349968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43148 q = 1) (hb : d271214 q = 1) : d350154 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43148, d350154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d42866 q = 1) (hb : d271214 q = 1) : d349969 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42866, d349969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43149 q = 1) (hb : d271214 q = 1) : d350155 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43149, d350155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43150 q = 1) (hb : d271214 q = 1) : d350156 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43150, d350156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43151 q = 1) (hb : d271214 q = 1) : d350157 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43151, d350157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43151, d350157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43156 q = 1) (hb : d271214 q = 1) : d350162 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43156, d350162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43156, d350162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43157 q = 1) (hb : d271214 q = 1) : d350163 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43157, d350163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43157, d350163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101204 (p : Pattern) (ha : d43173 p = 1) (hb : d271214 p = 1) : d350179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43153 q = 1) (hb : d271214 q = 1) : d350159 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43153, d350159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101201 q ha hb
    | true =>
      simp only [d43153, d350159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101202 q ha hb
  have h2 (q : Pattern) (ha : d43154 q = 1) (hb : d271214 q = 1) : d350160 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43154, d350160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43154, d350160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43155 q = 1) (hb : d271214 q = 1) : d350161 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43155, d350161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43155, d350161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43158 q = 1) (hb : d271214 q = 1) : d350164 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43158, d350164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101202 q ha hb
    | true =>
      simp only [d43158, d350164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101203 q ha hb
  have h5 (q : Pattern) (ha : d43159 q = 1) (hb : d271214 q = 1) : d350165 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43159, d350165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43159, d350165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43160 q = 1) (hb : d271214 q = 1) : d350166 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43160, d350166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43160, d350166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43161 q = 1) (hb : d271214 q = 1) : d350167 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43161, d350167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43161, d350167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43164 q = 1) (hb : d271214 q = 1) : d350170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43164, d350170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101202 q ha hb
    | true =>
      simp only [d43164, d350170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101172 q ha hb
  have h9 (q : Pattern) (ha : d43165 q = 1) (hb : d271214 q = 1) : d350171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43165, d350171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43165, d350171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43166 q = 1) (hb : d271214 q = 1) : d350172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43166, d350172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43166, d350172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43168 q = 1) (hb : d271214 q = 1) : d350174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d350174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101172 q ha hb
    | true =>
      simp only [d43168, d350174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101173 q ha hb
  have h12 (q : Pattern) (ha : d43169 q = 1) (hb : d271214 q = 1) : d350175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d350175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43169, d350175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43170 q = 1) (hb : d271214 q = 1) : d350176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d350176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43170, d350176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43171 q = 1) (hb : d271214 q = 1) : d350177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43171, d350177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43171, d350177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43172 q = 1) (hb : d271214 q = 1) : d350178 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43172, d350178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43172, d350178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d43173 q = 1) (hb : d271214 q = 1) : d350179 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43173, d350179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43173, d350179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro101205 (p : Pattern) (ha : d43178 p = 1) (hb : d271214 p = 1) : d350184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43164 q = 1) (hb : d271214 q = 1) : d350170 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43164, d350170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101202 q ha hb
    | true =>
      simp only [d43164, d350170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101172 q ha hb
  have h2 (q : Pattern) (ha : d43165 q = 1) (hb : d271214 q = 1) : d350171 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43165, d350171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43165, d350171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43166 q = 1) (hb : d271214 q = 1) : d350172 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43166, d350172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43166, d350172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43168 q = 1) (hb : d271214 q = 1) : d350174 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43168, d350174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101172 q ha hb
    | true =>
      simp only [d43168, d350174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101173 q ha hb
  have h5 (q : Pattern) (ha : d43169 q = 1) (hb : d271214 q = 1) : d350175 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43169, d350175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43169, d350175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43170 q = 1) (hb : d271214 q = 1) : d350176 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43170, d350176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43170, d350176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43171 q = 1) (hb : d271214 q = 1) : d350177 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43171, d350177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43171, d350177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43176 q = 1) (hb : d271214 q = 1) : d350182 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43176, d350182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43176, d350182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43177 q = 1) (hb : d271214 q = 1) : d350183 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43177, d350183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43177, d350183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43178 q = 1) (hb : d271214 q = 1) : d350184 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43178, d350184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43178, d350184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro101206 (p : Pattern) (ha : d43184 p = 1) (hb : d271214 p = 1) : d350190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43174 q = 1) (hb : d271214 q = 1) : d350180 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43174, d350180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101204 q ha hb
    | true =>
      simp only [d43174, d350180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43175 q = 1) (hb : d271214 q = 1) : d350181 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43175, d350181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43175, d350181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43179 q = 1) (hb : d271214 q = 1) : d350185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d350185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101205 q ha hb
    | true =>
      simp only [d43179, d350185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43180 q = 1) (hb : d271214 q = 1) : d350186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d350186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43180, d350186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43181 q = 1) (hb : d271214 q = 1) : d350187 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43181, d350187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43181, d350187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43182 q = 1) (hb : d271214 q = 1) : d350188 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43182, d350188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43182, d350188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43183 q = 1) (hb : d271214 q = 1) : d350189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43183, d350189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43183, d350189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43184 q = 1) (hb : d271214 q = 1) : d350190 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43184, d350190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43184, d350190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101207 (p : Pattern) (ha : d43192 p = 1) (hb : d271214 p = 1) : d350198 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43179 q = 1) (hb : d271214 q = 1) : d350185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d350185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101205 q ha hb
    | true =>
      simp only [d43179, d350185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43180 q = 1) (hb : d271214 q = 1) : d350186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d350186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43180, d350186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43187 q = 1) (hb : d271214 q = 1) : d350193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43187, d350193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101174 q ha hb
    | true =>
      simp only [d43187, d350193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43188 q = 1) (hb : d271214 q = 1) : d350194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43188, d350194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43188, d350194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43189 q = 1) (hb : d271214 q = 1) : d350195 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43189, d350195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43189, d350195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43190 q = 1) (hb : d271214 q = 1) : d350196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43190, d350196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43190, d350196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43191 q = 1) (hb : d271214 q = 1) : d350197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43191, d350197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43191, d350197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43192 q = 1) (hb : d271214 q = 1) : d350198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43192, d350198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43192, d350198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101208 (p : Pattern) (ha : d43246 p = 1) (hb : d271214 p = 1) : d350204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43179 q = 1) (hb : d271214 q = 1) : d350185 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43179, d350185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101205 q ha hb
    | true =>
      simp only [d43179, d350185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43180 q = 1) (hb : d271214 q = 1) : d350186 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43180, d350186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43180, d350186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43243 q = 1) (hb : d271214 q = 1) : d350201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43243, d350201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43243, d350201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43244 q = 1) (hb : d271214 q = 1) : d350202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43244, d350202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43244, d350202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43245 q = 1) (hb : d271214 q = 1) : d350203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43245, d350203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43245, d350203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43246 q = 1) (hb : d271214 q = 1) : d350204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43246, d350204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43246, d350204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101209 (p : Pattern) (ha : d271214 p = 1) (hb : d309910 p = 1) : d350210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43193 q = 1) (hb : d271214 q = 1) : d350199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43193, d350199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101206 q ha hb
    | true =>
      simp only [d43193, d350199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101207 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309906 q = 1) : d350200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d309906, d350200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d309906, d350200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d43247 q = 1) (hb : d271214 q = 1) : d350205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43247, d350205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101208 q ha hb
    | true =>
      simp only [d43247, d350205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43248 q = 1) (hb : d271214 q = 1) : d350206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43248, d350206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43248, d350206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309907 q = 1) : d350207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d309907, d350207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d309907, d350207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309908 q = 1) : d350208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d309908, d350208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309908, d350208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d271214 q = 1) (hb : d309909 q = 1) : d350209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d309909, d350209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309909, d350209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309910 q = 1) : d350210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d309910, d350210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309910, d350210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101210 (p : Pattern) (ha : d271214 p = 1) (hb : d309916 p = 1) : d350227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42905 q = 1) (hb : d271214 q = 1) : d350008 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42905, d350008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d42905, d350008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101165 q ha hb
  have h2 (q : Pattern) (ha : d42906 q = 1) (hb : d271214 q = 1) : d350009 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42906, d350009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d42906, d350009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d42915 q = 1) (hb : d271214 q = 1) : d350018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d42915, d350018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101165 q ha hb
    | true =>
      simp only [d42915, d350018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101168 q ha hb
  have h4 (q : Pattern) (ha : d42916 q = 1) (hb : d271214 q = 1) : d350019 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d42916, d350019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42916, d350019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d42917 q = 1) (hb : d271214 q = 1) : d350020 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d42917, d350020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d42917, d350020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309894 q = 1) : d350111 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309894, d350111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101192 q ha hb
    | true =>
      simp only [d309894, d350111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101199 q ha hb
  have h7 (q : Pattern) (ha : d43118 q = 1) (hb : d271214 q = 1) : d350124 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43118, d350124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101169 q ha hb
    | true =>
      simp only [d43118, d350124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101170 q ha hb
  have h8 (q : Pattern) (ha : d271214 q = 1) (hb : d309895 q = 1) : d350125 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309895, d350125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d309895, d350125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d271214 q = 1) (hb : d309896 q = 1) : d350126 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309896, d350126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d309896, d350126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d271214 q = 1) (hb : d309897 q = 1) : d350127 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309897, d350127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d309897, d350127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d271214 q = 1) (hb : d309901 q = 1) : d350131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309901, d350131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309901, d350131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101200 q ha hb
  have h12 (q : Pattern) (ha : d43127 q = 1) (hb : d271214 q = 1) : d350133 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43127, d350133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43127, d350133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101171 q ha hb
  have h13 (q : Pattern) (ha : d271214 q = 1) (hb : d309902 q = 1) : d350134 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309902, d350134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d309902, d350134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d271214 q = 1) (hb : d309903 q = 1) : d350135 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309903, d350135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d309903, d350135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d271214 q = 1) (hb : d309904 q = 1) : d350136 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309904, d350136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d309904, d350136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d271214 q = 1) (hb : d309905 q = 1) : d350137 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309905, d350137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d309905, d350137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d271214 q = 1) (hb : d309911 q = 1) : d350211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d309911, d350211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309911, d350211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101209 q ha hb
  have h18 (q : Pattern) (ha : d43264 q = 1) (hb : d271214 q = 1) : d350222 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43264, d350222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43264, d350222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101176 q ha hb
  have h19 (q : Pattern) (ha : d271214 q = 1) (hb : d309912 q = 1) : d350223 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d309912, d350223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d309912, d350223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d271214 q = 1) (hb : d309913 q = 1) : d350224 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d309913, d350224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d309913, d350224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d271214 q = 1) (hb : d309914 q = 1) : d350225 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d309914, d350225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d309914, d350225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d271214 q = 1) (hb : d309915 q = 1) : d350226 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d309915, d350226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d309915, d350226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d271214 q = 1) (hb : d309916 q = 1) : d350227 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d309916, d350227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d309916, d350227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro101211 (p : Pattern) (ha : d271214 p = 1) (hb : d309922 p = 1) : d350233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d271214 q = 1) (hb : d309917 q = 1) : d350228 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d309917, d350228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309917, d350228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101210 q ha hb
  have h2 (q : Pattern) (ha : d271214 q = 1) (hb : d309918 q = 1) : d350229 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d309918, d350229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309918, d350229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d271214 q = 1) (hb : d309919 q = 1) : d350230 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d309919, d350230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309919, d350230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d271214 q = 1) (hb : d309920 q = 1) : d350231 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d309920, d350231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309920, d350231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d271214 q = 1) (hb : d309921 q = 1) : d350232 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d309921, d350232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309921, d350232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d271214 q = 1) (hb : d309922 q = 1) : d350233 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d309922, d350233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d309922, d350233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101212 (p : Pattern) (ha : d1087 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1084 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1085 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1086 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1087 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101213 (p : Pattern) (ha : d1093 p = 1) (hb : d271214 p = 1) : d38813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1084 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1085 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1086 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d17 q = 1) (hb : d271214 q = 1) : d17 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1093 q = 1) (hb : d271214 q = 1) : d38813 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d1093, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1093, d38813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101214 (p : Pattern) (ha : d43288 p = 1) (hb : d271214 p = 1) : d350241 p = 1 := by
  have h0 (q : Pattern) (ha : d42938 q = 1) (hb : d271214 q = 1) : d42938 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43278 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101212 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d43279 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43280 q = 1) (hb : d271214 q = 1) : d350038 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43280, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43280, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42942 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101181 q ha hb
    | true =>
      simp only [d42942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d42943 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d42946 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101182 q ha hb
    | true =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d42947 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d42948 q = 1) (hb : d271214 q = 1) : d350039 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42948, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43281 q = 1) (hb : d271214 q = 1) : d350040 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43281, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43281, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43282 q = 1) (hb : d271214 q = 1) : d350041 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43282, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43282, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d43283 q = 1) (hb : d271214 q = 1) : d350236 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101213 q ha hb
  have h13 (q : Pattern) (ha : d43284 q = 1) (hb : d271214 q = 1) : d350237 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d43285 q = 1) (hb : d271214 q = 1) : d350238 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d350238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43285, d350238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d42951 q = 1) (hb : d271214 q = 1) : d349788 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42951, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42951, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d43286 q = 1) (hb : d271214 q = 1) : d350239 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43286, d350239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43286, d350239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43287 q = 1) (hb : d271214 q = 1) : d350240 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43287, d350240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43287, d350240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d43288 q = 1) (hb : d271214 q = 1) : d350241 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43288, d350241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43288, d350241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro101215 (p : Pattern) (ha : d9771 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1084 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1085 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1086 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d9771 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro101216 (p : Pattern) (ha : d43300 p = 1) (hb : d271214 p = 1) : d350246 p = 1 := by
  have h0 (q : Pattern) (ha : d43278 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101212 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43279 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43283 q = 1) (hb : d271214 q = 1) : d350236 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101213 q ha hb
  have h4 (q : Pattern) (ha : d43284 q = 1) (hb : d271214 q = 1) : d350237 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d43285 q = 1) (hb : d271214 q = 1) : d350238 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d350238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43285, d350238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42602 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101129 q ha hb
    | true =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d42603 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d42604 q = 1) (hb : d271214 q = 1) : d349788 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43293 q = 1) (hb : d271214 q = 1) : d350239 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43293, d350239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43293, d350239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43294 q = 1) (hb : d271214 q = 1) : d350240 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43294, d350240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43294, d350240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d43295 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43295, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101184 q ha hb
    | true =>
      simp only [d43295, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101215 q ha hb
  have h14 (q : Pattern) (ha : d43296 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43296, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43296, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d43297 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43297, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43297, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d43298 q = 1) (hb : d271214 q = 1) : d349802 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43298, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43298, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h17 (q : Pattern) (ha : d43299 q = 1) (hb : d271214 q = 1) : d349803 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43299, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43299, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d43300 q = 1) (hb : d271214 q = 1) : d350246 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43300, d350246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43300, d350246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro101217 (p : Pattern) (ha : d43309 p = 1) (hb : d271214 p = 1) : d350055 p = 1 := by
  have h0 (q : Pattern) (ha : d43278 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101212 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43279 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42962 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101184 q ha hb
    | true =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d42963 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d43306 q = 1) (hb : d271214 q = 1) : d349784 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43306, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43306, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43307 q = 1) (hb : d271214 q = 1) : d350053 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43307, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43307, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d43308 q = 1) (hb : d271214 q = 1) : d350054 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43308, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43308, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d43295 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43295, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101184 q ha hb
    | true =>
      simp only [d43295, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101215 q ha hb
  have h9 (q : Pattern) (ha : d43296 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43296, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43296, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d43297 q = 1) (hb : d271214 q = 1) : d349606 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43297, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43297, d349606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43298 q = 1) (hb : d271214 q = 1) : d349802 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43298, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43298, d349802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d43299 q = 1) (hb : d271214 q = 1) : d349803 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43299, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43299, d349803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d43309 q = 1) (hb : d271214 q = 1) : d350055 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43309, d350055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43309, d350055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101218 (p : Pattern) (ha : d43318 p = 1) (hb : d271214 p = 1) : d350256 p = 1 := by
  have h0 (q : Pattern) (ha : d43283 q = 1) (hb : d271214 q = 1) : d350236 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101213 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43284 q = 1) (hb : d271214 q = 1) : d350237 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d43314 q = 1) (hb : d271214 q = 1) : d350252 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43314, d350252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43314, d350252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43315 q = 1) (hb : d271214 q = 1) : d350253 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43315, d350253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43315, d350253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d43316 q = 1) (hb : d271214 q = 1) : d350254 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43316, d350254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43316, d350254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43317 q = 1) (hb : d271214 q = 1) : d350255 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43317, d350255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43317, d350255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d1119 q = 1) (hb : d271214 q = 1) : d1119 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d43318 q = 1) (hb : d271214 q = 1) : d350256 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43318, d350256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43318, d350256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro101219 (p : Pattern) (ha : d43324 p = 1) (hb : d271214 p = 1) : d350262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43289 q = 1) (hb : d271214 q = 1) : d350242 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43289, d350242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101214 q ha hb
    | true =>
      simp only [d43289, d350242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43290 q = 1) (hb : d271214 q = 1) : d350243 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43290, d350243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43290, d350243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43291 q = 1) (hb : d271214 q = 1) : d350244 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43291, d350244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43291, d350244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43292 q = 1) (hb : d271214 q = 1) : d350245 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43292, d350245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43292, d350245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43301 q = 1) (hb : d271214 q = 1) : d350247 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43301, d350247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101216 q ha hb
    | true =>
      simp only [d43301, d350247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43302 q = 1) (hb : d271214 q = 1) : d350248 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43302, d350248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43302, d350248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43303 q = 1) (hb : d271214 q = 1) : d350249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43303, d350249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43303, d350249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43304 q = 1) (hb : d271214 q = 1) : d350250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43304, d350250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43304, d350250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43305 q = 1) (hb : d271214 q = 1) : d350251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43305, d350251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43305, d350251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43310 q = 1) (hb : d271214 q = 1) : d350056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43310, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101217 q ha hb
    | true =>
      simp only [d43310, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43311 q = 1) (hb : d271214 q = 1) : d350057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43311, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43311, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d43312 q = 1) (hb : d271214 q = 1) : d350058 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43312, d350058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43312, d350058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43313 q = 1) (hb : d271214 q = 1) : d350059 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43313, d350059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43313, d350059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43319 q = 1) (hb : d271214 q = 1) : d350257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d350257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101218 q ha hb
    | true =>
      simp only [d43319, d350257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43320 q = 1) (hb : d271214 q = 1) : d350258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d350258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43320, d350258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43321 q = 1) (hb : d271214 q = 1) : d350259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43321, d350259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43321, d350259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43322 q = 1) (hb : d271214 q = 1) : d350260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43322, d350260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43322, d350260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43323 q = 1) (hb : d271214 q = 1) : d350261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43323, d350261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43323, d350261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43324 q = 1) (hb : d271214 q = 1) : d350262 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43324, d350262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43324, d350262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro101220 (p : Pattern) (ha : d43330 p = 1) (hb : d271214 p = 1) : d350268 p = 1 := by
  have h0 (q : Pattern) (ha : d43278 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101212 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43279 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43283 q = 1) (hb : d271214 q = 1) : d350236 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101213 q ha hb
  have h4 (q : Pattern) (ha : d43284 q = 1) (hb : d271214 q = 1) : d350237 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d43285 q = 1) (hb : d271214 q = 1) : d350238 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43285, d350238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43285, d350238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d42602 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101129 q ha hb
    | true =>
      simp only [d42602, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d42603 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42603, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d42604 q = 1) (hb : d271214 q = 1) : d349788 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42604, d349788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43293 q = 1) (hb : d271214 q = 1) : d350239 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43293, d350239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43293, d350239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43294 q = 1) (hb : d271214 q = 1) : d350240 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43294, d350240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43294, d350240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d18 q = 1) (hb : d271214 q = 1) : d18 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d43325 q = 1) (hb : d271214 q = 1) : d350263 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43325, d350263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d43325, d350263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43326 q = 1) (hb : d271214 q = 1) : d350264 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43326, d350264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43326, d350264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d43327 q = 1) (hb : d271214 q = 1) : d350265 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43327, d350265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43327, d350265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43328 q = 1) (hb : d271214 q = 1) : d350266 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43328, d350266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43328, d350266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d43329 q = 1) (hb : d271214 q = 1) : d350267 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43329, d350267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43329, d350267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h21 (q : Pattern) (ha : d43330 q = 1) (hb : d271214 q = 1) : d350268 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43330, d350268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43330, d350268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro101221 (p : Pattern) (ha : d43335 p = 1) (hb : d271214 p = 1) : d350273 p = 1 := by
  have h0 (q : Pattern) (ha : d43283 q = 1) (hb : d271214 q = 1) : d350236 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101089 q ha hb
    | true =>
      simp only [d43283, d350236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101213 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43284 q = 1) (hb : d271214 q = 1) : d350237 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43284, d350237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18 q = 1) (hb : d271214 q = 1) : d18 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d43325 q = 1) (hb : d271214 q = 1) : d350263 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43325, d350263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d43325, d350263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43326 q = 1) (hb : d271214 q = 1) : d350264 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43326, d350264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43326, d350264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d43327 q = 1) (hb : d271214 q = 1) : d350265 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43327, d350265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43327, d350265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d42250 q = 1) (hb : d271214 q = 1) : d349492 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101070 q ha hb
    | true =>
      simp only [d42250, d349492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d42251 q = 1) (hb : d271214 q = 1) : d349493 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42251, d349493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d20 q = 1) (hb : d271214 q = 1) : d20 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d42252 q = 1) (hb : d271214 q = 1) : d349494 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d42252, d349494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43328 q = 1) (hb : d271214 q = 1) : d350266 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43328, d350266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43328, d350266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43329 q = 1) (hb : d271214 q = 1) : d350267 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43329, d350267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43329, d350267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d1119 q = 1) (hb : d271214 q = 1) : d1119 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d43335 q = 1) (hb : d271214 q = 1) : d350273 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43335, d350273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43335, d350273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro101222 (p : Pattern) (ha : d43342 p = 1) (hb : d271214 p = 1) : d350280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43331 q = 1) (hb : d271214 q = 1) : d350269 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43331, d350269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101220 q ha hb
    | true =>
      simp only [d43331, d350269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43332 q = 1) (hb : d271214 q = 1) : d350270 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43332, d350270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43332, d350270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43333 q = 1) (hb : d271214 q = 1) : d350271 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43333, d350271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43333, d350271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43334 q = 1) (hb : d271214 q = 1) : d350272 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43334, d350272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43334, d350272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43336 q = 1) (hb : d271214 q = 1) : d350274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101221 q ha hb
    | true =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43337 q = 1) (hb : d271214 q = 1) : d350275 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43338 q = 1) (hb : d271214 q = 1) : d350276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43338, d350276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43338, d350276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43339 q = 1) (hb : d271214 q = 1) : d350277 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43339, d350277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43339, d350277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43340 q = 1) (hb : d271214 q = 1) : d350278 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43340, d350278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43340, d350278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43319 q = 1) (hb : d271214 q = 1) : d350257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d350257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101218 q ha hb
    | true =>
      simp only [d43319, d350257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43320 q = 1) (hb : d271214 q = 1) : d350258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d350258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43320, d350258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d43321 q = 1) (hb : d271214 q = 1) : d350259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43321, d350259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43321, d350259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43322 q = 1) (hb : d271214 q = 1) : d350260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43322, d350260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43322, d350260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43341 q = 1) (hb : d271214 q = 1) : d350279 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43341, d350279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43341, d350279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43342 q = 1) (hb : d271214 q = 1) : d350280 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43342, d350280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43342, d350280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro101223 (p : Pattern) (ha : d43347 p = 1) (hb : d271214 p = 1) : d350285 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43336 q = 1) (hb : d271214 q = 1) : d350274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101221 q ha hb
    | true =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43337 q = 1) (hb : d271214 q = 1) : d350275 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43338 q = 1) (hb : d271214 q = 1) : d350276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43338, d350276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43338, d350276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43339 q = 1) (hb : d271214 q = 1) : d350277 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43339, d350277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43339, d350277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43346 q = 1) (hb : d271214 q = 1) : d350284 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43346, d350284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43346, d350284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d271214 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d43347 q = 1) (hb : d271214 q = 1) : d350285 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43347, d350285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43347, d350285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro101224 (p : Pattern) (ha : d43354 p = 1) (hb : d271214 p = 1) : d350292 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43343 q = 1) (hb : d271214 q = 1) : d350281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43343, d350281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101219 q ha hb
    | true =>
      simp only [d43343, d350281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101222 q ha hb
  have h2 (q : Pattern) (ha : d43344 q = 1) (hb : d271214 q = 1) : d350282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43344, d350282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43344, d350282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43345 q = 1) (hb : d271214 q = 1) : d350283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43345, d350283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43345, d350283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43348 q = 1) (hb : d271214 q = 1) : d350286 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d350286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101222 q ha hb
    | true =>
      simp only [d43348, d350286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101223 q ha hb
  have h5 (q : Pattern) (ha : d43349 q = 1) (hb : d271214 q = 1) : d350287 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d350287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43349, d350287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43350 q = 1) (hb : d271214 q = 1) : d350288 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d350288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43350, d350288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43351 q = 1) (hb : d271214 q = 1) : d350289 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43351, d350289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43351, d350289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43352 q = 1) (hb : d271214 q = 1) : d350290 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43352, d350290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43352, d350290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43353 q = 1) (hb : d271214 q = 1) : d350291 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43353, d350291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43353, d350291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43354 q = 1) (hb : d271214 q = 1) : d350292 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43354, d350292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43354, d350292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro101225 (p : Pattern) (ha : d43358 p = 1) (hb : d271214 p = 1) : d350296 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43348 q = 1) (hb : d271214 q = 1) : d350286 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43348, d350286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101222 q ha hb
    | true =>
      simp only [d43348, d350286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101223 q ha hb
  have h2 (q : Pattern) (ha : d43349 q = 1) (hb : d271214 q = 1) : d350287 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43349, d350287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43349, d350287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43350 q = 1) (hb : d271214 q = 1) : d350288 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43350, d350288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43350, d350288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43352 q = 1) (hb : d271214 q = 1) : d350290 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43352, d350290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43352, d350290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43357 q = 1) (hb : d271214 q = 1) : d350295 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43357, d350295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43357, d350295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43358 q = 1) (hb : d271214 q = 1) : d350296 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43358, d350296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43358, d350296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101226 (p : Pattern) (ha : d43364 p = 1) (hb : d271214 p = 1) : d350302 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d271214 q = 1) : d350293 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101224 q ha hb
    | true =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d271214 q = 1) : d350294 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d271214 q = 1) : d350299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43362 q = 1) (hb : d271214 q = 1) : d350300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d350300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d350300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43363 q = 1) (hb : d271214 q = 1) : d350301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43363, d350301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43363, d350301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43364 q = 1) (hb : d271214 q = 1) : d350302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43364, d350302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43364, d350302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101227 (p : Pattern) (ha : d43368 p = 1) (hb : d271214 p = 1) : d350306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d271214 q = 1) : d350303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43366 q = 1) (hb : d271214 q = 1) : d350304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d350304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d350304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43367 q = 1) (hb : d271214 q = 1) : d350305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43367, d350305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43367, d350305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43368 q = 1) (hb : d271214 q = 1) : d350306 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43368, d350306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43368, d350306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101228 (p : Pattern) (ha : d43374 p = 1) (hb : d271214 p = 1) : d350312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43369 q = 1) (hb : d271214 q = 1) : d350307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101226 q ha hb
    | true =>
      simp only [d43369, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101227 q ha hb
  have h2 (q : Pattern) (ha : d43370 q = 1) (hb : d271214 q = 1) : d350308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43370, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43371 q = 1) (hb : d271214 q = 1) : d350309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43372 q = 1) (hb : d271214 q = 1) : d350310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43372, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43373 q = 1) (hb : d271214 q = 1) : d350311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43373, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43374 q = 1) (hb : d271214 q = 1) : d350312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43374, d350312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43374, d350312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101229 (p : Pattern) (ha : d43377 p = 1) (hb : d271214 p = 1) : d350315 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d271214 q = 1) : d350293 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101224 q ha hb
    | true =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d271214 q = 1) : d350294 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d271214 q = 1) : d350299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43362 q = 1) (hb : d271214 q = 1) : d350300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d350300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d350300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43363 q = 1) (hb : d271214 q = 1) : d350301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43363, d350301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43363, d350301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43377 q = 1) (hb : d271214 q = 1) : d350315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43377, d350315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43377, d350315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro101230 (p : Pattern) (ha : d43378 p = 1) (hb : d271214 p = 1) : d350316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d271214 q = 1) : d350303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43366 q = 1) (hb : d271214 q = 1) : d350304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d350304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d350304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43367 q = 1) (hb : d271214 q = 1) : d350305 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43367, d350305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43367, d350305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43378 q = 1) (hb : d271214 q = 1) : d350316 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43378, d350316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43378, d350316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101231 (p : Pattern) (ha : d43384 p = 1) (hb : d271214 p = 1) : d350322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43369 q = 1) (hb : d271214 q = 1) : d350307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101226 q ha hb
    | true =>
      simp only [d43369, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101227 q ha hb
  have h2 (q : Pattern) (ha : d43370 q = 1) (hb : d271214 q = 1) : d350308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43370, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43371 q = 1) (hb : d271214 q = 1) : d350309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43372 q = 1) (hb : d271214 q = 1) : d350310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43372, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43373 q = 1) (hb : d271214 q = 1) : d350311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43373, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43379 q = 1) (hb : d271214 q = 1) : d350317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43379, d350317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101229 q ha hb
    | true =>
      simp only [d43379, d350317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101230 q ha hb
  have h7 (q : Pattern) (ha : d43380 q = 1) (hb : d271214 q = 1) : d350318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43380, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43380, d350318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43381 q = 1) (hb : d271214 q = 1) : d350319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43381, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43381, d350319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43382 q = 1) (hb : d271214 q = 1) : d350320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43382, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43382, d350320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43383 q = 1) (hb : d271214 q = 1) : d350321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43383, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43383, d350321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43384 q = 1) (hb : d271214 q = 1) : d350322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43384, d350322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43384, d350322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101232 (p : Pattern) (ha : d43630 p = 1) (hb : d271214 p = 1) : d350427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43369 q = 1) (hb : d271214 q = 1) : d350307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43369, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101226 q ha hb
    | true =>
      simp only [d43369, d350307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101227 q ha hb
  have h2 (q : Pattern) (ha : d43370 q = 1) (hb : d271214 q = 1) : d350308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43370, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43370, d350308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43371 q = 1) (hb : d271214 q = 1) : d350309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43371, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43371, d350309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43372 q = 1) (hb : d271214 q = 1) : d350310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43372, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43372, d350310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43373 q = 1) (hb : d271214 q = 1) : d350311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43373, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43373, d350311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43625 q = 1) (hb : d271214 q = 1) : d350422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43625, d350422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101227 q ha hb
    | true =>
      simp only [d43625, d350422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43626 q = 1) (hb : d271214 q = 1) : d350423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43626, d350423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43626, d350423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43627 q = 1) (hb : d271214 q = 1) : d350424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43627, d350424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43627, d350424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43628 q = 1) (hb : d271214 q = 1) : d350425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43628, d350425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43628, d350425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43629 q = 1) (hb : d271214 q = 1) : d350426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43629, d350426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43629, d350426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43630 q = 1) (hb : d271214 q = 1) : d350427 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43630, d350427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43630, d350427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101233 (p : Pattern) (ha : d43636 p = 1) (hb : d271214 p = 1) : d350433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43625 q = 1) (hb : d271214 q = 1) : d350422 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43625, d350422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101227 q ha hb
    | true =>
      simp only [d43625, d350422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43626 q = 1) (hb : d271214 q = 1) : d350423 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43626, d350423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43626, d350423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43627 q = 1) (hb : d271214 q = 1) : d350424 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43627, d350424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43627, d350424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43628 q = 1) (hb : d271214 q = 1) : d350425 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43628, d350425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43628, d350425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43629 q = 1) (hb : d271214 q = 1) : d350426 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43629, d350426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43629, d350426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43631 q = 1) (hb : d271214 q = 1) : d350428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43631, d350428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101230 q ha hb
    | true =>
      simp only [d43631, d350428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43632 q = 1) (hb : d271214 q = 1) : d350429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43632, d350429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43632, d350429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43633 q = 1) (hb : d271214 q = 1) : d350430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43633, d350430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43633, d350430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43634 q = 1) (hb : d271214 q = 1) : d350431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43634, d350431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43634, d350431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43635 q = 1) (hb : d271214 q = 1) : d350432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43635, d350432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43635, d350432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43636 q = 1) (hb : d271214 q = 1) : d350433 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43636, d350433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43636, d350433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro101234 (p : Pattern) (ha : d43645 p = 1) (hb : d271214 p = 1) : d350442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43631 q = 1) (hb : d271214 q = 1) : d350428 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43631, d350428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101230 q ha hb
    | true =>
      simp only [d43631, d350428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43632 q = 1) (hb : d271214 q = 1) : d350429 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43632, d350429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43632, d350429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43633 q = 1) (hb : d271214 q = 1) : d350430 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43633, d350430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43633, d350430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43634 q = 1) (hb : d271214 q = 1) : d350431 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43634, d350431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43634, d350431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43635 q = 1) (hb : d271214 q = 1) : d350432 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43635, d350432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43635, d350432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43645 q = 1) (hb : d271214 q = 1) : d350442 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43645, d350442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43645, d350442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101235 (p : Pattern) (ha : d43708 p = 1) (hb : d271214 p = 1) : d350496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43699 q = 1) (hb : d271214 q = 1) : d350487 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43699, d350487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43699, d350487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101220 q ha hb
  have h2 (q : Pattern) (ha : d43331 q = 1) (hb : d271214 q = 1) : d350269 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43331, d350269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101220 q ha hb
    | true =>
      simp only [d43331, d350269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43700 q = 1) (hb : d271214 q = 1) : d350488 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43700, d350488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43700, d350488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43332 q = 1) (hb : d271214 q = 1) : d350270 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43332, d350270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43332, d350270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43701 q = 1) (hb : d271214 q = 1) : d350489 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43701, d350489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43701, d350489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43702 q = 1) (hb : d271214 q = 1) : d350490 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43702, d350490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43702, d350490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43703 q = 1) (hb : d271214 q = 1) : d350491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43703, d350491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43703, d350491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101221 q ha hb
  have h8 (q : Pattern) (ha : d43336 q = 1) (hb : d271214 q = 1) : d350274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101221 q ha hb
    | true =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43704 q = 1) (hb : d271214 q = 1) : d350492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43704, d350492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43704, d350492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43337 q = 1) (hb : d271214 q = 1) : d350275 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43705 q = 1) (hb : d271214 q = 1) : d350493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43705, d350493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43705, d350493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d43706 q = 1) (hb : d271214 q = 1) : d350494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43706, d350494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43706, d350494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d43707 q = 1) (hb : d271214 q = 1) : d350495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43707, d350495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43707, d350495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43679 q = 1) (hb : d271214 q = 1) : d350472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43679, d350472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43679, d350472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101218 q ha hb
  have h15 (q : Pattern) (ha : d43319 q = 1) (hb : d271214 q = 1) : d350257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43319, d350257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101218 q ha hb
    | true =>
      simp only [d43319, d350257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43680 q = 1) (hb : d271214 q = 1) : d350473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43680, d350473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43680, d350473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43320 q = 1) (hb : d271214 q = 1) : d350258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43320, d350258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d43320, d350258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43681 q = 1) (hb : d271214 q = 1) : d350474 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43681, d350474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43681, d350474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43682 q = 1) (hb : d271214 q = 1) : d350475 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43682, d350475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d43682, d350475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d43693 q = 1) (hb : d271214 q = 1) : d350481 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43693, d350481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d43693, d350481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d43708 q = 1) (hb : d271214 q = 1) : d350496 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43708, d350496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43708, d350496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro101236 (p : Pattern) (ha : d43713 p = 1) (hb : d271214 p = 1) : d350501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43703 q = 1) (hb : d271214 q = 1) : d350491 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43703, d350491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43703, d350491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101221 q ha hb
  have h2 (q : Pattern) (ha : d43336 q = 1) (hb : d271214 q = 1) : d350274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101221 q ha hb
    | true =>
      simp only [d43336, d350274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43704 q = 1) (hb : d271214 q = 1) : d350492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43704, d350492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43704, d350492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43337 q = 1) (hb : d271214 q = 1) : d350275 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43337, d350275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43705 q = 1) (hb : d271214 q = 1) : d350493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43705, d350493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43705, d350493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43706 q = 1) (hb : d271214 q = 1) : d350494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43706, d350494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43706, d350494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43712 q = 1) (hb : d271214 q = 1) : d350500 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43712, d350500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43712, d350500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15023 q = 1) (hb : d271214 q = 1) : d15023 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d43713 q = 1) (hb : d271214 q = 1) : d350501 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43713, d350501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43713, d350501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro101237 (p : Pattern) (ha : d43732 p = 1) (hb : d271214 p = 1) : d350520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43714 q = 1) (hb : d271214 q = 1) : d350502 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d43714, d350502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101235 q ha hb
    | true =>
      simp only [d43714, d350502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101236 q ha hb
  have h2 (q : Pattern) (ha : d43715 q = 1) (hb : d271214 q = 1) : d350503 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d43715, d350503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43715, d350503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43716 q = 1) (hb : d271214 q = 1) : d350504 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d43716, d350504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43716, d350504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43722 q = 1) (hb : d271214 q = 1) : d350510 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d43722, d350510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43722, d350510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43731 q = 1) (hb : d271214 q = 1) : d350519 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d43731, d350519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43731, d350519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43732 q = 1) (hb : d271214 q = 1) : d350520 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d43732, d350520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43732, d350520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101238 (p : Pattern) (ha : d43821 p = 1) (hb : d271214 p = 1) : d350552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43733 q = 1) (hb : d271214 q = 1) : d350521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43733, d350521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101237 q ha hb
    | true =>
      simp only [d43733, d350521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43734 q = 1) (hb : d271214 q = 1) : d350522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43734, d350522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43734, d350522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43818 q = 1) (hb : d271214 q = 1) : d350549 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43818, d350549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43818, d350549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43819 q = 1) (hb : d271214 q = 1) : d350550 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43819, d350550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43819, d350550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43820 q = 1) (hb : d271214 q = 1) : d350551 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43820, d350551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43820, d350551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43821 q = 1) (hb : d271214 q = 1) : d350552 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43821, d350552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43821, d350552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro101239 (p : Pattern) (ha : d43827 p = 1) (hb : d271214 p = 1) : d350558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43822 q = 1) (hb : d271214 q = 1) : d350553 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43822, d350553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101238 q ha hb
    | true =>
      simp only [d43822, d350553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43823 q = 1) (hb : d271214 q = 1) : d350554 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d43823, d350554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43823, d350554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43824 q = 1) (hb : d271214 q = 1) : d350555 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d43824, d350555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43824, d350555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43825 q = 1) (hb : d271214 q = 1) : d350556 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d43825, d350556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43825, d350556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43826 q = 1) (hb : d271214 q = 1) : d350557 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d43826, d350557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43826, d350557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43827 q = 1) (hb : d271214 q = 1) : d350558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d43827, d350558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43827, d350558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101240 (p : Pattern) (ha : d43389 p = 1) (hb : d271214 p = 1) : d350327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d271214 q = 1) : d350293 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101224 q ha hb
    | true =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d271214 q = 1) : d350294 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d271214 q = 1) : d350299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43362 q = 1) (hb : d271214 q = 1) : d350300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43362, d350300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43362, d350300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43388 q = 1) (hb : d271214 q = 1) : d350326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43388, d350326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43388, d350326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43389 q = 1) (hb : d271214 q = 1) : d350327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43389, d350327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43389, d350327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101241 (p : Pattern) (ha : d43391 p = 1) (hb : d271214 p = 1) : d350329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d271214 q = 1) : d350303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43366 q = 1) (hb : d271214 q = 1) : d350304 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43366, d350304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43366, d350304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43390 q = 1) (hb : d271214 q = 1) : d350328 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43390, d350328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43390, d350328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43391 q = 1) (hb : d271214 q = 1) : d350329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43391, d350329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43391, d350329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101242 (p : Pattern) (ha : d43398 p = 1) (hb : d271214 p = 1) : d350336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43355 q = 1) (hb : d271214 q = 1) : d350293 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101224 q ha hb
    | true =>
      simp only [d43355, d350293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43356 q = 1) (hb : d271214 q = 1) : d350294 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43356, d350294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43361 q = 1) (hb : d271214 q = 1) : d350299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43361, d350299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43396 q = 1) (hb : d271214 q = 1) : d350334 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43396, d350334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43396, d350334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43397 q = 1) (hb : d271214 q = 1) : d350335 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43397, d350335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43397, d350335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d43398 q = 1) (hb : d271214 q = 1) : d350336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43398, d350336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43398, d350336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101243 (p : Pattern) (ha : d43401 p = 1) (hb : d271214 p = 1) : d350339 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43359 q = 1) (hb : d271214 q = 1) : d350297 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101225 q ha hb
    | true =>
      simp only [d43359, d350297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43360 q = 1) (hb : d271214 q = 1) : d350298 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43360, d350298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43365 q = 1) (hb : d271214 q = 1) : d350303 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43365, d350303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d43399 q = 1) (hb : d271214 q = 1) : d350337 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d43399, d350337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43399, d350337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43400 q = 1) (hb : d271214 q = 1) : d350338 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d43400, d350338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43400, d350338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43401 q = 1) (hb : d271214 q = 1) : d350339 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d43401, d350339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43401, d350339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro101244 (p : Pattern) (ha : d43406 p = 1) (hb : d271214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2005 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d14 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1084 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1084, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d1085 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d42940 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d43406 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro101245 (p : Pattern) (ha : d43415 p = 1) (hb : d271214 p = 1) : d350343 p = 1 := by
  have h0 (q : Pattern) (ha : d43405 q = 1) (hb : d271214 q = 1) : d43405 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43407 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101244 q ha hb
    | true =>
      simp only [d43407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43408 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d43409 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43410 q = 1) (hb : d271214 q = 1) : d44004 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43410, d44004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43410, d44004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43411 q = 1) (hb : d271214 q = 1) : d44005 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43411, d44005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43411, d44005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d42938 q = 1) (hb : d271214 q = 1) : d42938 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d43278 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101212 q ha hb
  have h9 (q : Pattern) (ha : d43279 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d43280 q = 1) (hb : d271214 q = 1) : d350038 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43280, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43280, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d42946 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101182 q ha hb
    | true =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d42947 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d43412 q = 1) (hb : d271214 q = 1) : d350039 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43412, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43412, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d43413 q = 1) (hb : d271214 q = 1) : d350040 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43413, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43413, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d43414 q = 1) (hb : d271214 q = 1) : d350041 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43414, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43414, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d43415 q = 1) (hb : d271214 q = 1) : d350343 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43415, d350343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43415, d350343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro101246 (p : Pattern) (ha : d43421 p = 1) (hb : d271214 p = 1) : d349781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271213 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1523 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1523, d271214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2001 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d34366 q = 1) (hb : d271214 q = 1) : d34366 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d42591 q = 1) (hb : d271214 q = 1) : d42935 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d42591, d42935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d42591, d42935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d43420 q = 1) (hb : d271214 q = 1) : d43420 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d43421 q = 1) (hb : d271214 q = 1) : d349781 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d43421, d349781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43421, d349781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro101247 (p : Pattern) (ha : d43427 p = 1) (hb : d271214 p = 1) : d350348 p = 1 := by
  have h0 (q : Pattern) (ha : d42938 q = 1) (hb : d271214 q = 1) : d42938 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43278 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101128 q ha hb
    | true =>
      simp only [d43278, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101212 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d43279 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43279, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43280 q = 1) (hb : d271214 q = 1) : d350038 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43280, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43280, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d42942 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101181 q ha hb
    | true =>
      simp only [d42942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d42943 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d42943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d42946 q = 1) (hb : d271214 q = 1) : d349786 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101182 q ha hb
    | true =>
      simp only [d42946, d349786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d42947 q = 1) (hb : d271214 q = 1) : d349787 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42947, d349787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d42948 q = 1) (hb : d271214 q = 1) : d350039 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d42948, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d42948, d350039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43281 q = 1) (hb : d271214 q = 1) : d350040 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43281, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43281, d350040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d43282 q = 1) (hb : d271214 q = 1) : d350041 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43282, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43282, d350041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d43422 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43422, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101246 q ha hb
    | true =>
      simp only [d43422, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d43423 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43423, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43423, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d42962 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101184 q ha hb
    | true =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d42963 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d43424 q = 1) (hb : d271214 q = 1) : d349784 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43424, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43424, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43425 q = 1) (hb : d271214 q = 1) : d350053 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43425, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43425, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h18 (q : Pattern) (ha : d43426 q = 1) (hb : d271214 q = 1) : d350054 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43426, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d43426, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d43427 q = 1) (hb : d271214 q = 1) : d350348 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43427, d350348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d43427, d350348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro101248 (p : Pattern) (ha : d43436 p = 1) (hb : d271214 p = 1) : d350356 p = 1 := by
  have h0 (q : Pattern) (ha : d42938 q = 1) (hb : d271214 q = 1) : d42938 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d43422 q = 1) (hb : d271214 q = 1) : d349782 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d43422, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101246 q ha hb
    | true =>
      simp only [d43422, d349782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d43423 q = 1) (hb : d271214 q = 1) : d349783 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d43423, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d43423, d349783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d43433 q = 1) (hb : d271214 q = 1) : d350038 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43433, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43433, d350038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d43434 q = 1) (hb : d271214 q = 1) : d350354 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43434, d350354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43434, d350354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d43435 q = 1) (hb : d271214 q = 1) : d350355 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43435, d350355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43435, d350355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d42962 q = 1) (hb : d271214 q = 1) : d349604 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101184 q ha hb
    | true =>
      simp only [d42962, d349604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d42963 q = 1) (hb : d271214 q = 1) : d349605 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d42963, d349605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d43424 q = 1) (hb : d271214 q = 1) : d349784 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d43424, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43424, d349784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43425 q = 1) (hb : d271214 q = 1) : d350053 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d43425, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43425, d350053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d43426 q = 1) (hb : d271214 q = 1) : d350054 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d43426, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43426, d350054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d43436 q = 1) (hb : d271214 q = 1) : d350356 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d43436, d350356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d43436, d350356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro101249 (p : Pattern) (ha : d43442 p = 1) (hb : d271214 p = 1) : d350362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271214 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d43416 q = 1) (hb : d271214 q = 1) : d350344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43416, d350344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101245 q ha hb
    | true =>
      simp only [d43416, d350344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d43417 q = 1) (hb : d271214 q = 1) : d350345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43417, d350345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d43417, d350345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d43418 q = 1) (hb : d271214 q = 1) : d350346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43418, d350346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43418, d350346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d43419 q = 1) (hb : d271214 q = 1) : d350347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43419, d350347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d43419, d350347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d43428 q = 1) (hb : d271214 q = 1) : d350349 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43428, d350349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101247 q ha hb
    | true =>
      simp only [d43428, d350349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d43429 q = 1) (hb : d271214 q = 1) : d350350 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43429, d350350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d43429, d350350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d43430 q = 1) (hb : d271214 q = 1) : d350351 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43430, d350351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43430, d350351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d43431 q = 1) (hb : d271214 q = 1) : d350352 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43431, d350352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d43431, d350352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d43432 q = 1) (hb : d271214 q = 1) : d350353 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43432, d350353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d43432, d350353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d43437 q = 1) (hb : d271214 q = 1) : d350357 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43437, d350357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101248 q ha hb
    | true =>
      simp only [d43437, d350357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d43438 q = 1) (hb : d271214 q = 1) : d350358 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43438, d350358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d43438, d350358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d43439 q = 1) (hb : d271214 q = 1) : d350359 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43439, d350359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43439, d350359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d43440 q = 1) (hb : d271214 q = 1) : d350360 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43440, d350360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d43440, d350360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d43310 q = 1) (hb : d271214 q = 1) : d350056 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43310, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101217 q ha hb
    | true =>
      simp only [d43310, d350056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d43311 q = 1) (hb : d271214 q = 1) : d350057 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43311, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d43311, d350057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d43312 q = 1) (hb : d271214 q = 1) : d350058 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d43312, d350058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d43312, d350058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d43313 q = 1) (hb : d271214 q = 1) : d350059 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d43313, d350059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d43313, d350059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d43441 q = 1) (hb : d271214 q = 1) : d350361 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d43441, d350361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d43441, d350361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d43442 q = 1) (hb : d271214 q = 1) : d350362 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d43442, d350362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d43442, d350362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
end NetHack.Soko22Hazard87
