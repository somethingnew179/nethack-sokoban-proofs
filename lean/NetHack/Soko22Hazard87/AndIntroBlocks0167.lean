import NetHack.Soko22Hazard87.AndIntroBlocks0166
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro41750 (p : Pattern) (ha : d129464 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129459 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41749 q ha hb
    | true =>
      simp only [d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129460 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129461 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129462 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129463 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129464 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41751 (p : Pattern) (ha : d129470 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129465 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41750 q ha hb
    | true =>
      simp only [d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129466 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129467 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129468 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129469 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129470 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41752 (p : Pattern) (ha : d0 p = 1) (hb : d187381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187381 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro41753 (p : Pattern) (ha : d61083 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17697 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41650 q ha hb
  have h2 (q : Pattern) (ha : d61079 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61080 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61081 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61082 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61083 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41754 (p : Pattern) (ha : d61093 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41647 q ha hb
    | true =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41642 q ha hb
  have h2 (q : Pattern) (ha : d61089 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61090 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61091 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61092 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61093 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41755 (p : Pattern) (ha : d61099 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61094 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41754 q ha hb
  have h2 (q : Pattern) (ha : d61095 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61096 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61097 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61098 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61099 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41756 (p : Pattern) (ha : d61105 p = 1) (hb : d163684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61084 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41753 q ha hb
  have h2 (q : Pattern) (ha : d61085 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61086 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61087 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61088 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61100 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41755 q ha hb
  have h7 (q : Pattern) (ha : d61101 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61102 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61103 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61104 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61105 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro41757 (p : Pattern) (ha : d163684 p = 1) (hb : d173535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41666 q hb ha
    | true =>
      simp only [d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41659 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41758 (p : Pattern) (ha : d163684 p = 1) (hb : d173541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41757 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41759 (p : Pattern) (ha : d163684 p = 1) (hb : d173547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41758 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41760 (p : Pattern) (ha : d163684 p = 1) (hb : d173554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41682 q hb ha
    | true =>
      simp only [d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41674 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41761 (p : Pattern) (ha : d163684 p = 1) (hb : d173560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41760 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41762 (p : Pattern) (ha : d163684 p = 1) (hb : d173566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41761 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41763 (p : Pattern) (ha : d163684 p = 1) (hb : d173570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17980 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41693 q ha hb
    | true =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
  have h2 (q : Pattern) (ha : d17981 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17982 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17990 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
    | true =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41695 q ha hb
  have h5 (q : Pattern) (ha : d17991 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17992 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17993 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18009 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41687 q ha hb
    | true =>
      simp only [d18009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41688 q ha hb
  have h9 (q : Pattern) (ha : d18010 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18011 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18012 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163684 q = 1) (hb : d173569 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d163684 q = 1) (hb : d173570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41764 (p : Pattern) (ha : d163684 p = 1) (hb : d173576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41763 q ha hb
    | true =>
      simp only [d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41689 q ha hb
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d163684 q = 1) (hb : d173575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d163684 q = 1) (hb : d173576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41765 (p : Pattern) (ha : d163684 p = 1) (hb : d173582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41764 q ha hb
    | true =>
      simp only [d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41690 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41766 (p : Pattern) (ha : d163684 p = 1) (hb : d173588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41765 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173588 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41767 (p : Pattern) (ha : d163684 p = 1) (hb : d173594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173589 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41766 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173590 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173591 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173592 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173593 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173594 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41768 (p : Pattern) (ha : d163684 p = 1) (hb : d173599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18161 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41712 q ha hb
    | true =>
      simp only [d18161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
  have h2 (q : Pattern) (ha : d18162 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18163 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18171 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
    | true =>
      simp only [d18171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41714 q ha hb
  have h5 (q : Pattern) (ha : d18172 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18173 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18174 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18192 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41706 q ha hb
    | true =>
      simp only [d18192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41707 q ha hb
  have h9 (q : Pattern) (ha : d18193 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18194 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18195 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163684 q = 1) (hb : d173598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d163684 q = 1) (hb : d173599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41769 (p : Pattern) (ha : d163684 p = 1) (hb : d173605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41768 q ha hb
    | true =>
      simp only [d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41708 q ha hb
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d163684 q = 1) (hb : d173604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d163684 q = 1) (hb : d173605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41770 (p : Pattern) (ha : d163684 p = 1) (hb : d173611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41769 q ha hb
    | true =>
      simp only [d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41709 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41771 (p : Pattern) (ha : d163684 p = 1) (hb : d173617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41770 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41772 (p : Pattern) (ha : d163684 p = 1) (hb : d173623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41771 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41773 (p : Pattern) (ha : d163684 p = 1) (hb : d173629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18342 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41731 q ha hb
    | true =>
      simp only [d18342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
  have h2 (q : Pattern) (ha : d18343 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18344 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18352 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
    | true =>
      simp only [d18352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41733 q ha hb
  have h5 (q : Pattern) (ha : d18353 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18354 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18355 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18373 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41725 q ha hb
    | true =>
      simp only [d18373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41726 q ha hb
  have h9 (q : Pattern) (ha : d18374 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18375 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18376 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163684 q = 1) (hb : d173628 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d163684 q = 1) (hb : d173629 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro41774 (p : Pattern) (ha : d163684 p = 1) (hb : d173635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173630 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41773 q ha hb
    | true =>
      simp only [d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173631 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41727 q ha hb
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d163684 q = 1) (hb : d173634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d163684 q = 1) (hb : d173635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41775 (p : Pattern) (ha : d163684 p = 1) (hb : d173641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41774 q ha hb
    | true =>
      simp only [d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41728 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173639 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173640 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41776 (p : Pattern) (ha : d163684 p = 1) (hb : d173647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41775 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41777 (p : Pattern) (ha : d163684 p = 1) (hb : d173653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41776 q ha hb
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41778 (p : Pattern) (ha : d163684 p = 1) (hb : d173659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d163684 q = 1) (hb : d173548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41756 q hb ha
    | true =>
      simp only [d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41759 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173567 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41762 q ha hb
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173568 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173595 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41767 q ha hb
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173596 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173597 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d163684 q = 1) (hb : d173624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41772 q ha hb
  have h8 (q : Pattern) (ha : d163684 q = 1) (hb : d173625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d163684 q = 1) (hb : d173626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163684 q = 1) (hb : d173627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d163684 q = 1) (hb : d173654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41777 q ha hb
  have h12 (q : Pattern) (ha : d163684 q = 1) (hb : d173655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163684 q = 1) (hb : d173656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d163684 q = 1) (hb : d173657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d163684 q = 1) (hb : d173658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d163684 q = 1) (hb : d173659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41779 (p : Pattern) (ha : d163684 p = 1) (hb : d173665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41778 q ha hb
    | true =>
      simp only [d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41780 (p : Pattern) (ha : d163684 p = 1) (hb : d173671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41779 q ha hb
    | true =>
      simp only [d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41781 (p : Pattern) (ha : d163684 p = 1) (hb : d173677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41780 q ha hb
    | true =>
      simp only [d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41782 (p : Pattern) (ha : d163684 p = 1) (hb : d173683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41781 q ha hb
    | true =>
      simp only [d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41783 (p : Pattern) (ha : d163684 p = 1) (hb : d173689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41782 q ha hb
    | true =>
      simp only [d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41784 (p : Pattern) (ha : d163684 p = 1) (hb : d173695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41783 q ha hb
    | true =>
      simp only [d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41785 (p : Pattern) (ha : d163684 p = 1) (hb : d173701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d163684 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163684 q = 1) (hb : d173696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41784 q ha hb
    | true =>
      simp only [d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d163684 q = 1) (hb : d173697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d163684 q = 1) (hb : d173698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d163684 q = 1) (hb : d173699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d163684 q = 1) (hb : d173700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d163684 q = 1) (hb : d173701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41786 (p : Pattern) (ha : d0 p = 1) (hb : d187673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187673 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro41787 (p : Pattern) (ha : d17570 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17566 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17567 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17568 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17569 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d17570 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro41788 (p : Pattern) (ha : d17576 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17571 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41787 q ha hb
    | true =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17572 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17573 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17574 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17575 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17576 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41789 (p : Pattern) (ha : d17582 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41788 q ha hb
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17578 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17579 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17580 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17581 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17582 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41790 (p : Pattern) (ha : d17588 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17583 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41789 q ha hb
  have h2 (q : Pattern) (ha : d17584 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17585 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17586 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17587 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17588 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41791 (p : Pattern) (ha : d17602 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17599 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17566 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17567 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17600 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17568 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17601 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17602 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro41792 (p : Pattern) (ha : d17608 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41791 q ha hb
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17571 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41787 q ha hb
    | true =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17572 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17605 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17606 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17607 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17608 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41793 (p : Pattern) (ha : d60563 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41792 q ha hb
    | true =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41788 q ha hb
  have h2 (q : Pattern) (ha : d60559 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17577 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41788 q ha hb
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17578 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60560 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d60561 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60562 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60563 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41794 (p : Pattern) (ha : d60569 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d60564 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41793 q ha hb
  have h2 (q : Pattern) (ha : d60565 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d60565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d60566 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d60566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d60567 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d60567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d60568 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d60569 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41795 (p : Pattern) (ha : d17696 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17577 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41788 q ha hb
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17692 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17693 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17694 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17695 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17696 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41796 (p : Pattern) (ha : d17655 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17652 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17598 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17599 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17653 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d17566 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17567 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17567, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d17600 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17654 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d17655 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro41797 (p : Pattern) (ha : d17661 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17656 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41796 q ha hb
    | true =>
      simp only [d17656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17657 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17603 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41791 q ha hb
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17604 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17658 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17659 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17660 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17661 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41798 (p : Pattern) (ha : d17684 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17603 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41791 q ha hb
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17604 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17681 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17682 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17683 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17684 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41799 (p : Pattern) (ha : d128580 p = 1) (hb : d129315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17662 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41797 q ha hb
    | true =>
      simp only [d17662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41792 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d17685 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41798 q ha hb
    | true =>
      simp only [d17685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17686 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d129315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41800 (p : Pattern) (ha : d128580 p = 1) (hb : d129321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41799 q ha hb
  have h2 (q : Pattern) (ha : d17697 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41795 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129317 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129318 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129319 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129320 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129321 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41801 (p : Pattern) (ha : d128580 p = 1) (hb : d129327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17589 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41790 q ha hb
  have h2 (q : Pattern) (ha : d17590 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17591 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17592 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d60570 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41794 q ha hb
  have h6 (q : Pattern) (ha : d60571 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d60572 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d60573 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d60573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d60574 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d60574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128580 q = 1) (hb : d129322 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41800 q ha hb
  have h11 (q : Pattern) (ha : d128580 q = 1) (hb : d129323 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128580 q = 1) (hb : d129324 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128580 q = 1) (hb : d129325 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128580 q = 1) (hb : d129326 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128580 q = 1) (hb : d129327 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41802 (p : Pattern) (ha : d17740 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17598 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17599 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17730 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17739 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d17740 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro41803 (p : Pattern) (ha : d17792 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17741 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41802 q ha hb
    | true =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17742 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17789 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17790 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17791 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17792 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41804 (p : Pattern) (ha : d17798 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17793 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41803 q ha hb
    | true =>
      simp only [d17793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17794 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17795 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17796 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17797 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17798 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41805 (p : Pattern) (ha : d17727 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17719 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17720 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17720, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17720, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17724 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17724, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17724, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17725 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d17651 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17652 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d17598 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17599 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17653 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17726 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d17727 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41806 (p : Pattern) (ha : d17732 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17652 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17652, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17598 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17599 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17599, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17653 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17730 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17731 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17732 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro41807 (p : Pattern) (ha : d17738 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17728 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41805 q ha hb
    | true =>
      simp only [d17728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17729 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17733 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41806 q ha hb
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17734 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17735 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17736 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17737 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17738 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41808 (p : Pattern) (ha : d17746 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41806 q ha hb
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17741 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41802 q ha hb
    | true =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17742 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17743 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17744 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17745 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17746 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41809 (p : Pattern) (ha : d17781 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17733 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41806 q ha hb
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17734 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17778 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17779 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17780 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17781 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41810 (p : Pattern) (ha : d128580 p = 1) (hb : d129332 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17747 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41807 q ha hb
    | true =>
      simp only [d17747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41808 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129328 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d17782 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41809 q ha hb
    | true =>
      simp only [d17782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17783 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129329 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129330 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129331 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d129332 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41811 (p : Pattern) (ha : d128580 p = 1) (hb : d129338 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129333 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41810 q ha hb
  have h2 (q : Pattern) (ha : d17799 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41804 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129334 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129335 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129336 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129337 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129338 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41812 (p : Pattern) (ha : d128580 p = 1) (hb : d129344 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129339 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41811 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129340 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129341 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129342 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129343 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129344 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41813 (p : Pattern) (ha : d17858 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17841 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17842 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17848 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17857 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d17858 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro41814 (p : Pattern) (ha : d17921 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17859 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41813 q ha hb
    | true =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17860 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17918 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17919 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17920 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17921 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41815 (p : Pattern) (ha : d17927 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17922 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41814 q ha hb
    | true =>
      simp only [d17922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17923 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17924 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17925 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17926 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17927 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41816 (p : Pattern) (ha : d17845 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17827 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17827, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17827, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17831 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17832 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17832, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17832, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17833 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d17837 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17838 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d17841 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17842 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17843 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17844 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d17845 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41817 (p : Pattern) (ha : d17850 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17838 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17838, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17841 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17842 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17842, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17843 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17848 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17849 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d17850 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d17850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro41818 (p : Pattern) (ha : d17856 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17846 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41816 q ha hb
    | true =>
      simp only [d17846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17847 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17851 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41817 q ha hb
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17852 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17853 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17854 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17855 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17856 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41819 (p : Pattern) (ha : d17864 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41817 q ha hb
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17859 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41813 q ha hb
    | true =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17860 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17861 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17862 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17863 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d17864 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41820 (p : Pattern) (ha : d17910 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17851 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41817 q ha hb
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17852 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17907 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17908 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17909 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d17910 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41821 (p : Pattern) (ha : d128580 p = 1) (hb : d129350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17865 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41818 q ha hb
    | true =>
      simp only [d17865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41819 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d17911 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41820 q ha hb
    | true =>
      simp only [d17911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d17912 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d129350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41822 (p : Pattern) (ha : d128580 p = 1) (hb : d129356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41821 q ha hb
  have h2 (q : Pattern) (ha : d17928 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41815 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129355 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129356 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41823 (p : Pattern) (ha : d128580 p = 1) (hb : d129362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129357 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41822 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129358 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129359 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129360 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129361 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129362 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41824 (p : Pattern) (ha : d18014 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18010 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18011 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18012 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18013 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d18014 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro41825 (p : Pattern) (ha : d18101 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18015 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41824 q ha hb
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18016 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18098 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18099 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18100 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18101 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41826 (p : Pattern) (ha : d18107 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18102 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41825 q ha hb
    | true =>
      simp only [d18102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18103 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18104 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18105 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18106 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18107 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41827 (p : Pattern) (ha : d17995 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17963 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17964 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17964, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17964, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17971 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17972 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17972, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17972, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17973 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d17981 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17982 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d17991 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d17992 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d17993 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17994 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d17995 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41828 (p : Pattern) (ha : d18000 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17982 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17992 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17993 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d17998 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17999 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18000 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro41829 (p : Pattern) (ha : d18006 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17996 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41827 q ha hb
    | true =>
      simp only [d17996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d17997 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18001 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41828 q ha hb
    | true =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18002 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18003 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18004 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18005 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18006 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41830 (p : Pattern) (ha : d18020 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18001 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41828 q ha hb
    | true =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18002 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41824 q ha hb
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18017 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18018 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18019 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18020 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41831 (p : Pattern) (ha : d18084 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17982 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17992 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17993 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18080 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18081 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18081, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18081, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18082 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18083 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18084 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro41832 (p : Pattern) (ha : d18090 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18085 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41831 q ha hb
    | true =>
      simp only [d18085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18086 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18087 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18088 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18089 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18090 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41833 (p : Pattern) (ha : d128580 p = 1) (hb : d129369 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18021 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41829 q ha hb
    | true =>
      simp only [d18021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41830 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129365 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18091 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41832 q ha hb
    | true =>
      simp only [d18091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18092 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129366 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d129369 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41834 (p : Pattern) (ha : d128580 p = 1) (hb : d129375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129370 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41833 q ha hb
  have h2 (q : Pattern) (ha : d18108 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41826 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129371 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129372 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129373 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129374 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129375 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41835 (p : Pattern) (ha : d128580 p = 1) (hb : d129381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129376 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41834 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129377 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129378 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129379 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129380 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129381 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41836 (p : Pattern) (ha : d18197 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18193 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18194 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18195 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18196 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d18197 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro41837 (p : Pattern) (ha : d18286 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18198 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41836 q ha hb
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18199 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18283 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18284 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18285 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18286 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41838 (p : Pattern) (ha : d18292 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18287 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41837 q ha hb
    | true =>
      simp only [d18287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18288 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18289 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18290 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18291 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18292 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41839 (p : Pattern) (ha : d18176 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18145 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18145, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18145, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18152 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18153 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18153, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18153, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18154 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18162 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18163 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d18172 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18173 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18174 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18175 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18176 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41840 (p : Pattern) (ha : d18181 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18163 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18172 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18173 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18174 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18179 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18180 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18181 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro41841 (p : Pattern) (ha : d18187 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18177 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41839 q ha hb
    | true =>
      simp only [d18177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18178 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18182 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41840 q ha hb
    | true =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18183 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18184 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18185 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18186 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18187 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41842 (p : Pattern) (ha : d18203 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18182 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41840 q ha hb
    | true =>
      simp only [d18182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18183 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41836 q ha hb
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18200 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18201 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18202 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18203 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41843 (p : Pattern) (ha : d18269 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18163 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18172 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18173 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18174 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18265 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18266 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18266, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18266, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18267 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18268 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18269 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro41844 (p : Pattern) (ha : d18275 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18270 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41843 q ha hb
    | true =>
      simp only [d18270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18271 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18272 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18273 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18274 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18275 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41845 (p : Pattern) (ha : d128580 p = 1) (hb : d129389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18204 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41841 q ha hb
    | true =>
      simp only [d18204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41842 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129385 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18276 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41844 q ha hb
    | true =>
      simp only [d18276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18277 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129386 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129387 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129388 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d129389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41846 (p : Pattern) (ha : d128580 p = 1) (hb : d129395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129390 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41845 q ha hb
  have h2 (q : Pattern) (ha : d18293 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41838 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129391 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129392 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129393 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129394 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129395 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41847 (p : Pattern) (ha : d128580 p = 1) (hb : d129401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129396 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41846 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129397 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129398 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129399 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129400 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129401 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41848 (p : Pattern) (ha : d18378 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18375 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18376 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18377 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d18378 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro41849 (p : Pattern) (ha : d18467 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18379 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41848 q ha hb
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18380 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18464 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18465 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18466 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18467 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41850 (p : Pattern) (ha : d18473 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18468 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41849 q ha hb
    | true =>
      simp only [d18468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18469 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18470 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18471 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18472 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18473 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41851 (p : Pattern) (ha : d18357 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18329 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18329, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18329, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18333 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18334 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18334, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18334, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18335 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18343 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18344 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d18353 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18354 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d18355 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18356 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18357 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro41852 (p : Pattern) (ha : d18362 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18344 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18353 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18354 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18355 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18360 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18361 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18362 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h9 p ha hb
theorem andIntro41853 (p : Pattern) (ha : d18368 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18358 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41851 q ha hb
    | true =>
      simp only [d18358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18359 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18363 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41852 q ha hb
    | true =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18364 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18365 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18366 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18367 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18368 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41854 (p : Pattern) (ha : d18384 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18363 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41852 q ha hb
    | true =>
      simp only [d18363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18364 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41848 q ha hb
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18381 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18382 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18383 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18384 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro41855 (p : Pattern) (ha : d18450 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18344 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18353 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18354 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18355 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18446 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18447 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18447, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18447, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18448 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18449 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18450 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h11 p ha hb
theorem andIntro41856 (p : Pattern) (ha : d18456 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18451 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41855 q ha hb
    | true =>
      simp only [d18451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18452 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18453 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18454 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18455 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18456 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41857 (p : Pattern) (ha : d128580 p = 1) (hb : d129410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18385 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41853 q ha hb
    | true =>
      simp only [d18385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41854 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18457 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41856 q ha hb
    | true =>
      simp only [d18457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18458 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d129410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41858 (p : Pattern) (ha : d128580 p = 1) (hb : d129416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41857 q ha hb
  have h2 (q : Pattern) (ha : d18474 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41850 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129412 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129413 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129414 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129415 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129416 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41859 (p : Pattern) (ha : d128580 p = 1) (hb : d129422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129417 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41858 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129418 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129419 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129420 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129421 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129422 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41860 (p : Pattern) (ha : d128580 p = 1) (hb : d129428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128580 q = 1) (hb : d129345 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41801 q ha hb
    | true =>
      simp only [d129345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41812 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129363 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41823 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129364 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129382 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41835 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129383 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129384 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d129402 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41847 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d129403 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128580 q = 1) (hb : d129404 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128580 q = 1) (hb : d129405 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128580 q = 1) (hb : d129423 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41859 q ha hb
  have h12 (q : Pattern) (ha : d128580 q = 1) (hb : d129424 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128580 q = 1) (hb : d129425 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128580 q = 1) (hb : d129426 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128580 q = 1) (hb : d129427 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128580 q = 1) (hb : d129428 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41861 (p : Pattern) (ha : d128580 p = 1) (hb : d129434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129429 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41860 q ha hb
    | true =>
      simp only [d129429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129430 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129431 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129432 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129433 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129434 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41862 (p : Pattern) (ha : d128580 p = 1) (hb : d129440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129435 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41861 q ha hb
    | true =>
      simp only [d129435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129436 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129437 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129438 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129439 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129440 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41863 (p : Pattern) (ha : d128580 p = 1) (hb : d129446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129441 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41862 q ha hb
    | true =>
      simp only [d129441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129442 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129443 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129444 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129445 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129446 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41864 (p : Pattern) (ha : d128580 p = 1) (hb : d129452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129447 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41863 q ha hb
    | true =>
      simp only [d129447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129448 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129449 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129450 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129451 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129452 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41865 (p : Pattern) (ha : d128580 p = 1) (hb : d129458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129453 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41864 q ha hb
    | true =>
      simp only [d129453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129454 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129455 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129456 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129457 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129458 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41866 (p : Pattern) (ha : d128580 p = 1) (hb : d129464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129459 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41865 q ha hb
    | true =>
      simp only [d129459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129460 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129461 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129462 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129463 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129464 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41867 (p : Pattern) (ha : d128580 p = 1) (hb : d129470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d129465 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41866 q ha hb
    | true =>
      simp only [d129465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d129466 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d129467 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d129468 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d129469 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d129470 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41868 (p : Pattern) (ha : d61083 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17697 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41795 q ha hb
  have h2 (q : Pattern) (ha : d61079 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61080 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61081 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61082 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61083 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41869 (p : Pattern) (ha : d61093 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17609 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41792 q ha hb
    | true =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41788 q ha hb
  have h2 (q : Pattern) (ha : d61089 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61090 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61091 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61092 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61093 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41870 (p : Pattern) (ha : d61099 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61094 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41869 q ha hb
  have h2 (q : Pattern) (ha : d61095 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d61095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d61096 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d61096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d61097 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d61097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d61098 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d61098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d61099 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41871 (p : Pattern) (ha : d61105 p = 1) (hb : d128580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d61084 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41868 q ha hb
  have h2 (q : Pattern) (ha : d61085 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d61086 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d61087 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d61088 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d61100 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41870 q ha hb
  have h7 (q : Pattern) (ha : d61101 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d61102 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d61103 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d61104 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d61104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d61105 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d61105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro41872 (p : Pattern) (ha : d128580 p = 1) (hb : d173535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41808 q hb ha
    | true =>
      simp only [d173530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41803 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41873 (p : Pattern) (ha : d128580 p = 1) (hb : d173541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41872 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41874 (p : Pattern) (ha : d128580 p = 1) (hb : d173547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41873 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41875 (p : Pattern) (ha : d128580 p = 1) (hb : d173554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41819 q hb ha
    | true =>
      simp only [d173549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41814 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41876 (p : Pattern) (ha : d128580 p = 1) (hb : d173560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41875 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41877 (p : Pattern) (ha : d128580 p = 1) (hb : d173566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41876 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41878 (p : Pattern) (ha : d128580 p = 1) (hb : d173570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17981 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17982 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17982, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17991 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d17992 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17992, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17993 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18010 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18011 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18011, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18012 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128580 q = 1) (hb : d173569 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d173569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d128580 q = 1) (hb : d173570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d173570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h11 p ha hb
theorem andIntro41879 (p : Pattern) (ha : d128580 p = 1) (hb : d173576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41878 q ha hb
    | true =>
      simp only [d173571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18015 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41824 q ha hb
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18016 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d173575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d173576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41880 (p : Pattern) (ha : d128580 p = 1) (hb : d173582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41879 q ha hb
    | true =>
      simp only [d173577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41825 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41881 (p : Pattern) (ha : d128580 p = 1) (hb : d173588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41880 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173588 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41882 (p : Pattern) (ha : d128580 p = 1) (hb : d173594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173589 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41881 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173590 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173591 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173592 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173593 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173594 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41883 (p : Pattern) (ha : d128580 p = 1) (hb : d173599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18163 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18163, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18172 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18173 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18173, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18174 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18193 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18194 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18194, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18194, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18195 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128580 q = 1) (hb : d173598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d173598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d128580 q = 1) (hb : d173599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d173599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h11 p ha hb
theorem andIntro41884 (p : Pattern) (ha : d128580 p = 1) (hb : d173605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41883 q ha hb
    | true =>
      simp only [d173600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18198 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41836 q ha hb
    | true =>
      simp only [d18198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18199 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d173604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d173605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41885 (p : Pattern) (ha : d128580 p = 1) (hb : d173611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41884 q ha hb
    | true =>
      simp only [d173606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41837 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173607 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173608 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173609 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173610 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41886 (p : Pattern) (ha : d128580 p = 1) (hb : d173617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41885 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173617 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41887 (p : Pattern) (ha : d128580 p = 1) (hb : d173623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173618 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41886 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173619 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173620 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173621 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173622 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173623 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41888 (p : Pattern) (ha : d128580 p = 1) (hb : d173629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128579 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d18343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d18344 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18344, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d18353 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18354 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18354, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d18355 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d18374 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18375 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18375, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18375, d128580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18376 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128580 q = 1) (hb : d173628 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d173628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d128580 q = 1) (hb : d173629 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d173629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  exact h11 p ha hb
theorem andIntro41889 (p : Pattern) (ha : d128580 p = 1) (hb : d173635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173630 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41888 q ha hb
    | true =>
      simp only [d173630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173631 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18379 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41848 q ha hb
    | true =>
      simp only [d18379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18380 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173632 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173633 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d173634 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d173635 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d173635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41890 (p : Pattern) (ha : d128580 p = 1) (hb : d173641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173636 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41889 q ha hb
    | true =>
      simp only [d173636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41849 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173637 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173638 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173639 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173640 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173641 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41891 (p : Pattern) (ha : d128580 p = 1) (hb : d173647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173642 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41890 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41892 (p : Pattern) (ha : d128580 p = 1) (hb : d173653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41891 q ha hb
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d173653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41893 (p : Pattern) (ha : d128580 p = 1) (hb : d173659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128580 q = 1) (hb : d173548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41871 q hb ha
    | true =>
      simp only [d173548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41874 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173567 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41877 q ha hb
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173568 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d173568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173595 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41882 q ha hb
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173596 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173597 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128580 q = 1) (hb : d173624 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41887 q ha hb
  have h8 (q : Pattern) (ha : d128580 q = 1) (hb : d173625 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128580 q = 1) (hb : d173626 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128580 q = 1) (hb : d173627 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d173627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128580 q = 1) (hb : d173654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41892 q ha hb
  have h12 (q : Pattern) (ha : d128580 q = 1) (hb : d173655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128580 q = 1) (hb : d173656 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128580 q = 1) (hb : d173657 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d173657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128580 q = 1) (hb : d173658 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d173658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128580 q = 1) (hb : d173659 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d173659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro41894 (p : Pattern) (ha : d128580 p = 1) (hb : d173665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173660 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41893 q ha hb
    | true =>
      simp only [d173660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173661 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173662 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173663 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173664 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173665 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41895 (p : Pattern) (ha : d128580 p = 1) (hb : d173671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173666 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41894 q ha hb
    | true =>
      simp only [d173666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173667 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173668 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173669 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173670 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173671 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41896 (p : Pattern) (ha : d128580 p = 1) (hb : d173677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173672 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41895 q ha hb
    | true =>
      simp only [d173672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173673 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173674 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173675 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173676 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173677 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41897 (p : Pattern) (ha : d128580 p = 1) (hb : d173683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173678 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41896 q ha hb
    | true =>
      simp only [d173678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173679 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173680 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173681 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173682 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173683 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41898 (p : Pattern) (ha : d128580 p = 1) (hb : d173689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173684 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41897 q ha hb
    | true =>
      simp only [d173684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173685 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173686 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173687 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173688 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173689 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41899 (p : Pattern) (ha : d128580 p = 1) (hb : d173695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173690 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41898 q ha hb
    | true =>
      simp only [d173690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173691 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173692 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173693 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173694 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173695 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41900 (p : Pattern) (ha : d128580 p = 1) (hb : d173701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128580 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128580 q = 1) (hb : d173696 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41899 q ha hb
    | true =>
      simp only [d173696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128580 q = 1) (hb : d173697 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d173697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128580 q = 1) (hb : d173698 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d173698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128580 q = 1) (hb : d173699 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d173699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128580 q = 1) (hb : d173700 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d173700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128580 q = 1) (hb : d173701 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d173701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41901 (p : Pattern) (ha : d129446 p = 1) (hb : d187676 p = 1) : d181585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d180908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129441 q = 1) (hb : d180908 q = 1) : d181580 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129441, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40932 q ha hb
    | true =>
      simp only [d129441, d181580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129442 q = 1) (hb : d180908 q = 1) : d181581 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129442, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129442, d181581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129443 q = 1) (hb : d180908 q = 1) : d181582 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129443, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129443, d181582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129444 q = 1) (hb : d180908 q = 1) : d181583 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129444, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129444, d181583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d129445 q = 1) (hb : d187676 q = 1) : d181584 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129445, d187676, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129445, d187676, d181584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d129446 q = 1) (hb : d187676 q = 1) : d181585 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129446, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129446, d181585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro41902 (p : Pattern) (ha : d129452 p = 1) (hb : d187676 p = 1) : d181591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129447 q = 1) (hb : d187676 q = 1) : d181586 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129447, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41901 q ha hb
    | true =>
      simp only [d129447, d181586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129448 q = 1) (hb : d187676 q = 1) : d181587 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129448, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129448, d181587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129449 q = 1) (hb : d187676 q = 1) : d181588 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129449, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129449, d181588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129450 q = 1) (hb : d187676 q = 1) : d181589 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129450, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129450, d181589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129451 q = 1) (hb : d187676 q = 1) : d181590 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129451, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129451, d181590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129452 q = 1) (hb : d187676 q = 1) : d181591 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129452, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129452, d181591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41903 (p : Pattern) (ha : d129458 p = 1) (hb : d187676 p = 1) : d181597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129453 q = 1) (hb : d187676 q = 1) : d181592 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129453, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41902 q ha hb
    | true =>
      simp only [d129453, d181592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129454 q = 1) (hb : d187676 q = 1) : d181593 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129454, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129454, d181593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129455 q = 1) (hb : d187676 q = 1) : d181594 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129455, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129455, d181594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129456 q = 1) (hb : d187676 q = 1) : d181595 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129456, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129456, d181595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129457 q = 1) (hb : d187676 q = 1) : d181596 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129457, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129457, d181596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129458 q = 1) (hb : d187676 q = 1) : d181597 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129458, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129458, d181597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41904 (p : Pattern) (ha : d129464 p = 1) (hb : d187676 p = 1) : d181603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129459 q = 1) (hb : d187676 q = 1) : d181598 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129459, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41903 q ha hb
    | true =>
      simp only [d129459, d181598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129460 q = 1) (hb : d187676 q = 1) : d181599 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129460, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129460, d181599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129461 q = 1) (hb : d187676 q = 1) : d181600 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129461, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129461, d181600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129462 q = 1) (hb : d187676 q = 1) : d181601 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129462, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129462, d181601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129463 q = 1) (hb : d187676 q = 1) : d181602 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129463, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129463, d181602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129464 q = 1) (hb : d187676 q = 1) : d181603 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129464, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129464, d181603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41905 (p : Pattern) (ha : d129470 p = 1) (hb : d187676 p = 1) : d181609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d187676 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129465 q = 1) (hb : d187676 q = 1) : d181604 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129465, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41904 q ha hb
    | true =>
      simp only [d129465, d181604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129466 q = 1) (hb : d187676 q = 1) : d181605 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129466, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129466, d181605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129467 q = 1) (hb : d187676 q = 1) : d181606 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129467, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129467, d181606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129468 q = 1) (hb : d187676 q = 1) : d181607 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129468, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129468, d181607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129469 q = 1) (hb : d187676 q = 1) : d181608 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129469, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129469, d181608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129470 q = 1) (hb : d187676 q = 1) : d181609 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129470, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129470, d181609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro41906 (p : Pattern) (ha : d51923 p = 1) (hb : d180912 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51920 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d51921 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d51922 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d51922, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51922, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d51923 q = 1) (hb : d180912 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d51923, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51923, d180912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41907 (p : Pattern) (ha : d130483 p = 1) (hb : d180918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51924 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51924, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
    | true =>
      simp only [d51924, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d51925 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51925, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51925, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51926 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51926, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51926, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51927 q = 1) (hb : d180916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d51927, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51927, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d51928 q = 1) (hb : d180917 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d51928, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51928, d180917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130483 q = 1) (hb : d180918 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130483, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130483, d180918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro41908 (p : Pattern) (ha : d130489 p = 1) (hb : d180924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130484 q = 1) (hb : d180919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130484, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41907 q ha hb
    | true =>
      simp only [d130484, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130485 q = 1) (hb : d180920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130485, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130485, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130486 q = 1) (hb : d180921 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130486, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130486, d180921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130487 q = 1) (hb : d180922 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130487, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130487, d180922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130488 q = 1) (hb : d180923 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130488, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130488, d180923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130489 q = 1) (hb : d180924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130489, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130489, d180924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41909 (p : Pattern) (ha : d130495 p = 1) (hb : d180930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130490 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130490, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41908 q ha hb
    | true =>
      simp only [d130490, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130491 q = 1) (hb : d180926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130491, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130491, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130492 q = 1) (hb : d180927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130492, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130492, d180927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130493 q = 1) (hb : d180928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130493, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130493, d180928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130494 q = 1) (hb : d180929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130494, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130494, d180929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130495 q = 1) (hb : d180930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130495, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130495, d180930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41910 (p : Pattern) (ha : d130501 p = 1) (hb : d180936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130496 q = 1) (hb : d180931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130496, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130496, d180931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41909 q ha hb
  have h2 (q : Pattern) (ha : d130497 q = 1) (hb : d180932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130497, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130497, d180932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130498 q = 1) (hb : d180933 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130498, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130498, d180933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130499 q = 1) (hb : d180934 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130499, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130499, d180934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130500 q = 1) (hb : d180935 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130500, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130500, d180935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130501 q = 1) (hb : d180936 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130501, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130501, d180936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41911 (p : Pattern) (ha : d52049 p = 1) (hb : d180944 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52046 q = 1) (hb : d180941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52046, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52046, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52047 q = 1) (hb : d180942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52047, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52047, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
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
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18534 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51920 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51921 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52048 q = 1) (hb : d180943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52048, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52048, d180943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51922 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d51922, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51922, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52049 q = 1) (hb : d180944 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52049, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52049, d180944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41912 (p : Pattern) (ha : d130506 p = 1) (hb : d180950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52050 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
    | true =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
  have h2 (q : Pattern) (ha : d52051 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52052 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51924 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51924, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
    | true =>
      simp only [d51924, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d51925 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51925, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51925, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51926 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51926, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51926, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52053 q = 1) (hb : d180948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52053, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52053, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51927 q = 1) (hb : d180916 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d51927, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51927, d180916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d52054 q = 1) (hb : d180949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52054, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52054, d180949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d130506 q = 1) (hb : d180950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130506, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130506, d180950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41913 (p : Pattern) (ha : d130512 p = 1) (hb : d180956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130507 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130507, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41912 q ha hb
    | true =>
      simp only [d130507, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130508 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130508, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130508, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130484 q = 1) (hb : d180919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130484, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41907 q ha hb
    | true =>
      simp only [d130484, d180919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130485 q = 1) (hb : d180920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130485, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130485, d180920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130509 q = 1) (hb : d180953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130509, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130509, d180953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130510 q = 1) (hb : d180954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130510, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130510, d180954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130511 q = 1) (hb : d180955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130511, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130511, d180955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130512 q = 1) (hb : d180956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130512, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130512, d180956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41914 (p : Pattern) (ha : d130518 p = 1) (hb : d180962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130513 q = 1) (hb : d180957 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130513, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41913 q ha hb
    | true =>
      simp only [d130513, d180957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41908 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130514 q = 1) (hb : d180958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130514, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130514, d180958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130490 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130490, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41908 q ha hb
    | true =>
      simp only [d130490, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130491 q = 1) (hb : d180926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130491, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130491, d180926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130515 q = 1) (hb : d180959 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130515, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130515, d180959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130516 q = 1) (hb : d180960 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130516, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130516, d180960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130517 q = 1) (hb : d180961 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130517, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130517, d180961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130518 q = 1) (hb : d180962 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130518, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130518, d180962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41915 (p : Pattern) (ha : d130524 p = 1) (hb : d180968 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130519 q = 1) (hb : d180963 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130519, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130519, d180963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41914 q ha hb
  have h2 (q : Pattern) (ha : d130520 q = 1) (hb : d180964 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130520, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130520, d180964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130521 q = 1) (hb : d180965 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130521, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130521, d180965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130522 q = 1) (hb : d180966 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130522, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130522, d180966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130523 q = 1) (hb : d180967 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130523, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130523, d180967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130524 q = 1) (hb : d180968 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130524, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130524, d180968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41916 (p : Pattern) (ha : d126912 p = 1) (hb : d180980 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52180 q = 1) (hb : d180974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52180, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52180, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52181 q = 1) (hb : d180975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52181, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52181, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d52044 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d52044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51990 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18571 q = 1) (hb : d52045 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18571, d52045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51991 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52046 q = 1) (hb : d180941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52046, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52046, d180941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d52047 q = 1) (hb : d180942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52047, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52047, d180942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52182 q = 1) (hb : d180976 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52182, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52182, d180976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18635 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d113009 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113009, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d113009, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d113010 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113010, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d113010, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d18534 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d51920 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51921 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d113011 q = 1) (hb : d180979 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d113011, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113011, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d126912 q = 1) (hb : d180980 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d126912, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d126912, d180980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41917 (p : Pattern) (ha : d130530 p = 1) (hb : d180986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126913 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d126913, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41916 q ha hb
    | true =>
      simp only [d126913, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
  have h2 (q : Pattern) (ha : d126914 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d126914, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126914, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d126915 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d126915, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126915, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52050 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
    | true =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
  have h5 (q : Pattern) (ha : d52051 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52052 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126916 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d126916, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126916, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51924 q = 1) (hb : d180913 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d51924, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
    | true =>
      simp only [d51924, d180913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d51925 q = 1) (hb : d180914 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d51925, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51925, d180914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51926 q = 1) (hb : d180915 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d51926, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51926, d180915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52053 q = 1) (hb : d180948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52053, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52053, d180948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126917 q = 1) (hb : d180985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d126917, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126917, d180985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d130530 q = 1) (hb : d180986 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130530, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130530, d180986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41918 (p : Pattern) (ha : d130536 p = 1) (hb : d180992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130531 q = 1) (hb : d180987 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130531, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41917 q ha hb
    | true =>
      simp only [d130531, d180987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130532 q = 1) (hb : d180988 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130532, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130532, d180988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130507 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130507, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41912 q ha hb
    | true =>
      simp only [d130507, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130508 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130508, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130508, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130533 q = 1) (hb : d180989 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130533, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130533, d180989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130534 q = 1) (hb : d180990 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130534, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130534, d180990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130535 q = 1) (hb : d180991 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130535, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130535, d180991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130536 q = 1) (hb : d180992 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130536, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130536, d180992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41919 (p : Pattern) (ha : d130542 p = 1) (hb : d180998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130507 q = 1) (hb : d180951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130507, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41912 q ha hb
    | true =>
      simp only [d130507, d180951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130508 q = 1) (hb : d180952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130508, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130508, d180952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130539 q = 1) (hb : d180995 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130539, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130539, d180995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130540 q = 1) (hb : d180996 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130540, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130540, d180996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130541 q = 1) (hb : d180997 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130541, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130541, d180997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130542 q = 1) (hb : d180998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130542, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130542, d180998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41920 (p : Pattern) (ha : d130548 p = 1) (hb : d181004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130537 q = 1) (hb : d180993 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130537, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41918 q ha hb
    | true =>
      simp only [d130537, d180993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41913 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130538 q = 1) (hb : d180994 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130538, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130538, d180994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130543 q = 1) (hb : d180999 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130543, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41919 q ha hb
    | true =>
      simp only [d130543, d180999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130544 q = 1) (hb : d181000 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130544, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130544, d181000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130545 q = 1) (hb : d181001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130545, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130545, d181001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130546 q = 1) (hb : d181002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130546, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130546, d181002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130547 q = 1) (hb : d181003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130547, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130547, d181003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130548 q = 1) (hb : d181004 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130548, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130548, d181004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41921 (p : Pattern) (ha : d130554 p = 1) (hb : d181010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130490 q = 1) (hb : d180925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130490, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41908 q ha hb
    | true =>
      simp only [d130490, d180925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130550 q = 1) (hb : d181006 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130550, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130550, d181006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130551 q = 1) (hb : d181007 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130551, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130551, d181007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130552 q = 1) (hb : d181008 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130552, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130552, d181008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130553 q = 1) (hb : d181009 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130553, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130553, d181009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130554 q = 1) (hb : d181010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130554, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130554, d181010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41922 (p : Pattern) (ha : d130560 p = 1) (hb : d181016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130549 q = 1) (hb : d181005 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130549, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130549, d181005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41920 q ha hb
  have h2 (q : Pattern) (ha : d130555 q = 1) (hb : d181011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130555, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130555, d181011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41921 q ha hb
  have h3 (q : Pattern) (ha : d130556 q = 1) (hb : d181012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130556, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130556, d181012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130557 q = 1) (hb : d181013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130557, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130557, d181013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130558 q = 1) (hb : d181014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130558, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130558, d181014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130559 q = 1) (hb : d181015 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130559, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130559, d181015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130560 q = 1) (hb : d181016 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130560, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130560, d181016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41923 (p : Pattern) (ha : d130566 p = 1) (hb : d181022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130502 q = 1) (hb : d180937 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130502, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130502, d180937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41910 q ha hb
  have h2 (q : Pattern) (ha : d130503 q = 1) (hb : d180938 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130503, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130503, d180938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130504 q = 1) (hb : d180939 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130504, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130504, d180939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130505 q = 1) (hb : d180940 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130505, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130505, d180940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130525 q = 1) (hb : d180969 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130525, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130525, d180969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41915 q ha hb
  have h6 (q : Pattern) (ha : d130526 q = 1) (hb : d180970 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130526, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130526, d180970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130527 q = 1) (hb : d180971 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130527, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130527, d180971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130528 q = 1) (hb : d180972 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130528, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130528, d180972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130529 q = 1) (hb : d180973 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130529, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130529, d180973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130561 q = 1) (hb : d181017 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130561, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130561, d181017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41922 q ha hb
  have h11 (q : Pattern) (ha : d130562 q = 1) (hb : d181018 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130562, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130562, d181018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130563 q = 1) (hb : d181019 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130563, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130563, d181019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130564 q = 1) (hb : d181020 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130564, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130564, d181020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130565 q = 1) (hb : d181021 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130565, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130565, d181021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130566 q = 1) (hb : d181022 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130566, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130566, d181022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41924 (p : Pattern) (ha : d127053 p = 1) (hb : d181031 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52365 q = 1) (hb : d181023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52365, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52365, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52366 q = 1) (hb : d181024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52366, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52366, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18711 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127049 q = 1) (hb : d181025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127049, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127049, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127050 q = 1) (hb : d181026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127050, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127050, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127051 q = 1) (hb : d181027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127051, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127051, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18715 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d113216 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d113217 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d113007 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d113007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23261 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d101015 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d18635 q = 1) (hb : d113008 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18635, d113008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d113009 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113009, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d113009, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d113010 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113010, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d113010, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d127052 q = 1) (hb : d181030 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127052, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127052, d181030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d127053 q = 1) (hb : d181031 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127053, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127053, d181031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41925 (p : Pattern) (ha : d127057 p = 1) (hb : d181035 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101017 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113009 q = 1) (hb : d180977 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113009, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113009, d180977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113010 q = 1) (hb : d180978 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113010, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113010, d180978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
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
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18534 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18534, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d51920 q = 1) (hb : d180909 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d51920, d180909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d51921 q = 1) (hb : d180910 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51921, d180910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113011 q = 1) (hb : d180979 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d113011, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113011, d180979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51922 q = 1) (hb : d180911 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d51922, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51922, d180911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d127057 q = 1) (hb : d181035 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127057, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127057, d181035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41926 (p : Pattern) (ha : d130567 p = 1) (hb : d181041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127054 q = 1) (hb : d181032 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127054, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41924 q ha hb
    | true =>
      simp only [d127054, d181032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41916 q ha hb
  have h2 (q : Pattern) (ha : d127055 q = 1) (hb : d181033 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127055, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127055, d181033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127056 q = 1) (hb : d181034 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127056, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127056, d181034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127058 q = 1) (hb : d181036 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127058, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41916 q ha hb
    | true =>
      simp only [d127058, d181036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41925 q ha hb
  have h5 (q : Pattern) (ha : d127059 q = 1) (hb : d181037 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127059, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127059, d181037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127060 q = 1) (hb : d181038 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127060, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127060, d181038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127061 q = 1) (hb : d181039 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127061, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127061, d181039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126913 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d126913, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41916 q ha hb
    | true =>
      simp only [d126913, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
  have h9 (q : Pattern) (ha : d126914 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d126914, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126914, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126915 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d126915, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126915, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52050 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
    | true =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
  have h12 (q : Pattern) (ha : d52051 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52052 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d126916 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d126916, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126916, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127062 q = 1) (hb : d181040 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127062, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127062, d181040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d130567 q = 1) (hb : d181041 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130567, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130567, d181041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro41927 (p : Pattern) (ha : d130570 p = 1) (hb : d181046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126913 q = 1) (hb : d180981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d126913, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41916 q ha hb
    | true =>
      simp only [d126913, d180981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
  have h2 (q : Pattern) (ha : d126914 q = 1) (hb : d180982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d126914, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126914, d180982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d126915 q = 1) (hb : d180983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d126915, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126915, d180983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52050 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
    | true =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
  have h5 (q : Pattern) (ha : d52051 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52052 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126916 q = 1) (hb : d180984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d126916, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126916, d180984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52377 q = 1) (hb : d181044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52377, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52377, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127066 q = 1) (hb : d181045 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127066, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127066, d181045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d130570 q = 1) (hb : d181046 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130570, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130570, d181046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41928 (p : Pattern) (ha : d130576 p = 1) (hb : d181052 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130568 q = 1) (hb : d181042 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130568, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41926 q ha hb
    | true =>
      simp only [d130568, d181042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130569 q = 1) (hb : d181043 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130569, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130569, d181043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130571 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130571, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41927 q ha hb
    | true =>
      simp only [d130571, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130572 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130572, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130572, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130573 q = 1) (hb : d181049 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130573, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130573, d181049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130574 q = 1) (hb : d181050 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130574, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130574, d181050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130575 q = 1) (hb : d181051 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130575, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130575, d181051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130576 q = 1) (hb : d181052 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130576, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130576, d181052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41929 (p : Pattern) (ha : d130577 p = 1) (hb : d181054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52050 q = 1) (hb : d180945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41911 q ha hb
    | true =>
      simp only [d52050, d180945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41906 q ha hb
  have h2 (q : Pattern) (ha : d52051 q = 1) (hb : d180946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52051, d180946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52052 q = 1) (hb : d180947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52052, d180947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52377 q = 1) (hb : d181044 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52377, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52377, d181044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52386 q = 1) (hb : d181053 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52386, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52386, d181053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130577 q = 1) (hb : d181054 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130577, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130577, d181054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro41930 (p : Pattern) (ha : d130583 p = 1) (hb : d181060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130571 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130571, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41927 q ha hb
    | true =>
      simp only [d130571, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130572 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130572, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130572, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130578 q = 1) (hb : d181055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130578, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41929 q ha hb
    | true =>
      simp only [d130578, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130579 q = 1) (hb : d181056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130579, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130579, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130580 q = 1) (hb : d181057 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130580, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130580, d181057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130581 q = 1) (hb : d181058 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130581, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130581, d181058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130582 q = 1) (hb : d181059 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130582, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130582, d181059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130583 q = 1) (hb : d181060 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130583, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130583, d181060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41931 (p : Pattern) (ha : d130594 p = 1) (hb : d181066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130571 q = 1) (hb : d181047 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130571, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41927 q ha hb
    | true =>
      simp only [d130571, d181047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130572 q = 1) (hb : d181048 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130572, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130572, d181048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130591 q = 1) (hb : d181063 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130591, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130591, d181063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130592 q = 1) (hb : d181064 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130592, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130592, d181064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130593 q = 1) (hb : d181065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130593, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130593, d181065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130594 q = 1) (hb : d181066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130594, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130594, d181066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41932 (p : Pattern) (ha : d130600 p = 1) (hb : d181072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130584 q = 1) (hb : d181061 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130584, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41928 q ha hb
    | true =>
      simp only [d130584, d181061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41930 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130590 q = 1) (hb : d181062 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130590, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130590, d181062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130595 q = 1) (hb : d181067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130595, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41931 q ha hb
    | true =>
      simp only [d130595, d181067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130596 q = 1) (hb : d181068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130596, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130596, d181068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130597 q = 1) (hb : d181069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130597, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130597, d181069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130598 q = 1) (hb : d181070 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130598, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130598, d181070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130599 q = 1) (hb : d181071 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130599, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130599, d181071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130600 q = 1) (hb : d181072 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130600, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130600, d181072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41933 (p : Pattern) (ha : d130588 p = 1) (hb : d181077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130578 q = 1) (hb : d181055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130578, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41929 q ha hb
    | true =>
      simp only [d130578, d181055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130579 q = 1) (hb : d181056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130579, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130579, d181056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130585 q = 1) (hb : d181074 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130585, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130585, d181074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130586 q = 1) (hb : d181075 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130586, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130586, d181075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130587 q = 1) (hb : d181076 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130587, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130587, d181076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130588 q = 1) (hb : d181077 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130588, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130588, d181077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41934 (p : Pattern) (ha : d130607 p = 1) (hb : d181083 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130602 q = 1) (hb : d181078 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130602, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41933 q ha hb
    | true =>
      simp only [d130602, d181078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130603 q = 1) (hb : d181079 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130603, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130603, d181079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130604 q = 1) (hb : d181080 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130604, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130604, d181080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130605 q = 1) (hb : d181081 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130605, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130605, d181081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130606 q = 1) (hb : d181082 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130606, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130606, d181082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130607 q = 1) (hb : d181083 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130607, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130607, d181083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41935 (p : Pattern) (ha : d130613 p = 1) (hb : d181089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130601 q = 1) (hb : d181073 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130601, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130601, d181073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41932 q ha hb
  have h2 (q : Pattern) (ha : d130608 q = 1) (hb : d181084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130608, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130608, d181084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41934 q ha hb
  have h3 (q : Pattern) (ha : d130609 q = 1) (hb : d181085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130609, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130609, d181085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130610 q = 1) (hb : d181086 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130610, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130610, d181086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130611 q = 1) (hb : d181087 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130611, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130611, d181087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130612 q = 1) (hb : d181088 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130612, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130612, d181088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130613 q = 1) (hb : d181089 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130613, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130613, d181089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41936 (p : Pattern) (ha : d130619 p = 1) (hb : d181095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130614 q = 1) (hb : d181090 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130614, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130614, d181090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41935 q ha hb
  have h2 (q : Pattern) (ha : d130615 q = 1) (hb : d181091 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130615, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130615, d181091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130616 q = 1) (hb : d181092 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130616, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130616, d181092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130617 q = 1) (hb : d181093 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130617, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130617, d181093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130618 q = 1) (hb : d181094 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130618, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130618, d181094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130619 q = 1) (hb : d181095 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130619, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130619, d181095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41937 (p : Pattern) (ha : d52600 p = 1) (hb : d181120 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52180 q = 1) (hb : d180974 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52180, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52180, d180974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52181 q = 1) (hb : d180975 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52181, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52181, d180975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
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
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18843 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52592 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d52593 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52594 q = 1) (hb : d181119 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52594, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52594, d181119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d52599 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52599, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52599, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d52600 q = 1) (hb : d181120 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52600, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d52600, d181120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41938 (p : Pattern) (ha : d52605 p = 1) (hb : d181124 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52592 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52593 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52599 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52599, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52599, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d52605 q = 1) (hb : d181124 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d52605, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d52605, d181124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41939 (p : Pattern) (ha : d127219 p = 1) (hb : d181105 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52512 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52586 q = 1) (hb : d181097 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52586, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52586, d181097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52587 q = 1) (hb : d181098 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52587, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52587, d181098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d16356 q = 1) (hb : d127213 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d127213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23290 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101167 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18834 q = 1) (hb : d127214 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18834, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18834, d127214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101169 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127215 q = 1) (hb : d181099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127215, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127215, d181099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127216 q = 1) (hb : d181100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127216, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127216, d181100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127217 q = 1) (hb : d181101 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127217, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127217, d181101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14644 q = 1) (hb : d122847 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d122847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23291 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101177 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18838 q = 1) (hb : d122848 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18838, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18838, d122848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101179 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d122849 q = 1) (hb : d181102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d122849, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d122849, d181102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d122850 q = 1) (hb : d181103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d122850, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d122850, d181103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d18715 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d113216 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d113217 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d127218 q = 1) (hb : d181104 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127218, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127218, d181104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d127219 q = 1) (hb : d181105 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127219, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127219, d181105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41940 (p : Pattern) (ha : d127220 p = 1) (hb : d181109 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52291 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52365 q = 1) (hb : d181023 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52365, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52365, d181023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52366 q = 1) (hb : d181024 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52366, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52366, d181024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d127047 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d127047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23272 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101073 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18711 q = 1) (hb : d127048 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18711, d127048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101075 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127049 q = 1) (hb : d181025 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127049, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127049, d181025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127050 q = 1) (hb : d181026 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127050, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127050, d181026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127051 q = 1) (hb : d181027 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127051, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127051, d181027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d113214 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d113214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23273 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101083 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18715 q = 1) (hb : d113215 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18715, d113215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d113216 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d113217 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d18843 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d52592 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d52593 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d113218 q = 1) (hb : d181108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d113218, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113218, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d127220 q = 1) (hb : d181109 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127220, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127220, d181109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41941 (p : Pattern) (ha : d127224 p = 1) (hb : d181114 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101085 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113216 q = 1) (hb : d181028 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113216, d181028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113217 q = 1) (hb : d181029 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113217, d181029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
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
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18843 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18843, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52592 q = 1) (hb : d181106 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52592, d181106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d52593 q = 1) (hb : d181107 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52593, d181107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113218 q = 1) (hb : d181108 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d113218, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113218, d181108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d52599 q = 1) (hb : d181113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52599, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d52599, d181113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d127224 q = 1) (hb : d181114 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127224, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127224, d181114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41942 (p : Pattern) (ha : d130621 p = 1) (hb : d181130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127221 q = 1) (hb : d181110 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127221, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41939 q ha hb
    | true =>
      simp only [d127221, d181110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41940 q ha hb
  have h2 (q : Pattern) (ha : d127222 q = 1) (hb : d181111 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127222, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127222, d181111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127223 q = 1) (hb : d181112 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127223, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127223, d181112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127225 q = 1) (hb : d181115 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127225, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41940 q ha hb
    | true =>
      simp only [d127225, d181115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41941 q ha hb
  have h5 (q : Pattern) (ha : d127226 q = 1) (hb : d181116 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127226, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127226, d181116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127227 q = 1) (hb : d181117 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127227, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127227, d181117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127228 q = 1) (hb : d181118 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127228, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127228, d181118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127229 q = 1) (hb : d181121 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127229, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41940 q ha hb
    | true =>
      simp only [d127229, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41937 q ha hb
  have h9 (q : Pattern) (ha : d127230 q = 1) (hb : d181122 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127230, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127230, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127231 q = 1) (hb : d181123 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127231, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127231, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d52606 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52606, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41937 q ha hb
    | true =>
      simp only [d52606, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41938 q ha hb
  have h12 (q : Pattern) (ha : d52607 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52607, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52607, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52608 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52608, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52608, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127232 q = 1) (hb : d181128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127232, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127232, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127233 q = 1) (hb : d181129 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127233, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127233, d181129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d130621 q = 1) (hb : d181130 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130621, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130621, d181130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro41943 (p : Pattern) (ha : d130624 p = 1) (hb : d181135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127229 q = 1) (hb : d181121 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127229, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41940 q ha hb
    | true =>
      simp only [d127229, d181121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41937 q ha hb
  have h2 (q : Pattern) (ha : d127230 q = 1) (hb : d181122 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127230, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127230, d181122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127231 q = 1) (hb : d181123 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127231, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127231, d181123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52606 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52606, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41937 q ha hb
    | true =>
      simp only [d52606, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41938 q ha hb
  have h5 (q : Pattern) (ha : d52607 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52607, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52607, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52608 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52608, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52608, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127232 q = 1) (hb : d181128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127232, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127232, d181128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52614 q = 1) (hb : d181133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52614, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52614, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127237 q = 1) (hb : d181134 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127237, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127237, d181134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d130624 q = 1) (hb : d181135 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130624, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130624, d181135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41944 (p : Pattern) (ha : d130630 p = 1) (hb : d181141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130622 q = 1) (hb : d181131 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130622, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41942 q ha hb
    | true =>
      simp only [d130622, d181131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130623 q = 1) (hb : d181132 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130623, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130623, d181132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130625 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130625, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41943 q ha hb
    | true =>
      simp only [d130625, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130626 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130626, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130626, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130627 q = 1) (hb : d181138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130627, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130627, d181138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130628 q = 1) (hb : d181139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130628, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130628, d181139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130629 q = 1) (hb : d181140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130629, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130629, d181140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130630 q = 1) (hb : d181141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130630, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130630, d181141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41945 (p : Pattern) (ha : d130631 p = 1) (hb : d181143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52606 q = 1) (hb : d181125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d52606, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41937 q ha hb
    | true =>
      simp only [d52606, d181125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41938 q ha hb
  have h2 (q : Pattern) (ha : d52607 q = 1) (hb : d181126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d52607, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52607, d181126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52608 q = 1) (hb : d181127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d52608, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52608, d181127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52614 q = 1) (hb : d181133 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d52614, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52614, d181133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d52623 q = 1) (hb : d181142 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d52623, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d52623, d181142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130631 q = 1) (hb : d181143 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130631, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130631, d181143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro41946 (p : Pattern) (ha : d130637 p = 1) (hb : d181149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130625 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130625, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41943 q ha hb
    | true =>
      simp only [d130625, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130626 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130626, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130626, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130632 q = 1) (hb : d181144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130632, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41945 q ha hb
    | true =>
      simp only [d130632, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130633 q = 1) (hb : d181145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130633, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130633, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130634 q = 1) (hb : d181146 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130634, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130634, d181146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130635 q = 1) (hb : d181147 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130635, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130635, d181147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130636 q = 1) (hb : d181148 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130636, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130636, d181148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130637 q = 1) (hb : d181149 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130637, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130637, d181149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41947 (p : Pattern) (ha : d130648 p = 1) (hb : d181155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130625 q = 1) (hb : d181136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130625, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41943 q ha hb
    | true =>
      simp only [d130625, d181136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130626 q = 1) (hb : d181137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130626, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130626, d181137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130645 q = 1) (hb : d181152 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130645, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130645, d181152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130646 q = 1) (hb : d181153 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130646, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130646, d181153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130647 q = 1) (hb : d181154 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130647, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130647, d181154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130648 q = 1) (hb : d181155 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130648, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130648, d181155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41948 (p : Pattern) (ha : d130654 p = 1) (hb : d181161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130638 q = 1) (hb : d181150 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130638, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41944 q ha hb
    | true =>
      simp only [d130638, d181150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41946 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130644 q = 1) (hb : d181151 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130644, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130644, d181151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130649 q = 1) (hb : d181156 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130649, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41947 q ha hb
    | true =>
      simp only [d130649, d181156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130650 q = 1) (hb : d181157 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130650, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130650, d181157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130651 q = 1) (hb : d181158 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130651, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130651, d181158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130652 q = 1) (hb : d181159 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130652, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130652, d181159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130653 q = 1) (hb : d181160 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130653, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130653, d181160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130654 q = 1) (hb : d181161 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130654, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130654, d181161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41949 (p : Pattern) (ha : d130642 p = 1) (hb : d181166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130632 q = 1) (hb : d181144 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130632, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41945 q ha hb
    | true =>
      simp only [d130632, d181144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130633 q = 1) (hb : d181145 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130633, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130633, d181145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130639 q = 1) (hb : d181163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130639, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130639, d181163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130640 q = 1) (hb : d181164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130640, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130640, d181164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130641 q = 1) (hb : d181165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130641, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130641, d181165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130642 q = 1) (hb : d181166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130642, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130642, d181166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41950 (p : Pattern) (ha : d130661 p = 1) (hb : d181172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130656 q = 1) (hb : d181167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130656, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41949 q ha hb
    | true =>
      simp only [d130656, d181167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130657 q = 1) (hb : d181168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130657, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130657, d181168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130658 q = 1) (hb : d181169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130658, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130658, d181169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130659 q = 1) (hb : d181170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130659, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130659, d181170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130660 q = 1) (hb : d181171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130660, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130660, d181171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130661 q = 1) (hb : d181172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130661, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130661, d181172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41951 (p : Pattern) (ha : d130667 p = 1) (hb : d181178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130655 q = 1) (hb : d181162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130655, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130655, d181162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41948 q ha hb
  have h2 (q : Pattern) (ha : d130662 q = 1) (hb : d181173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130662, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130662, d181173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41950 q ha hb
  have h3 (q : Pattern) (ha : d130663 q = 1) (hb : d181174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130663, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130663, d181174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130664 q = 1) (hb : d181175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130664, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130664, d181175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130665 q = 1) (hb : d181176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130665, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130665, d181176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130666 q = 1) (hb : d181177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130666, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130666, d181177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130667 q = 1) (hb : d181178 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130667, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130667, d181178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41952 (p : Pattern) (ha : d130673 p = 1) (hb : d181184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130668 q = 1) (hb : d181179 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130668, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130668, d181179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41951 q ha hb
  have h2 (q : Pattern) (ha : d130669 q = 1) (hb : d181180 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130669, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130669, d181180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130670 q = 1) (hb : d181181 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130670, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130670, d181181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130671 q = 1) (hb : d181182 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130671, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130671, d181182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130672 q = 1) (hb : d181183 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130672, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130672, d181183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130673 q = 1) (hb : d181184 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130673, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130673, d181184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41953 (p : Pattern) (ha : d123149 p = 1) (hb : d181234 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69109 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76092 q = 1) (hb : d181228 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d76092, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76092, d181228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76093 q = 1) (hb : d181229 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d76093, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76093, d181229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d76094 q = 1) (hb : d181230 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d76094, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76094, d181230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19046 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123146 q = 1) (hb : d181231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123146, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123146, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123147 q = 1) (hb : d181232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123147, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123147, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123148 q = 1) (hb : d181233 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123148, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123148, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123149 q = 1) (hb : d181234 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123149, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123149, d181234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41954 (p : Pattern) (ha : d127456 p = 1) (hb : d181197 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52792 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52866 q = 1) (hb : d181187 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52866, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52866, d181187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52867 q = 1) (hb : d181188 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52867, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52867, d181188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d16649 q = 1) (hb : d127450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d127450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23310 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101274 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d18994 q = 1) (hb : d127451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18994, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18994, d127451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101276 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127452 q = 1) (hb : d181189 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127452, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127452, d181189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127453 q = 1) (hb : d181190 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127453, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127453, d181190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127454 q = 1) (hb : d181191 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127454, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127454, d181191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14987 q = 1) (hb : d123112 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d123112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23311 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101284 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d18998 q = 1) (hb : d123113 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18998, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18998, d123113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101286 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d123114 q = 1) (hb : d181192 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123114, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d123114, d181192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d123115 q = 1) (hb : d181193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123115, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d123115, d181193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d19001 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d123121 q = 1) (hb : d181194 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123121, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d123121, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d123122 q = 1) (hb : d181195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123122, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d123122, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d127455 q = 1) (hb : d181196 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127455, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127455, d181196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d127456 q = 1) (hb : d181197 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127456, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127456, d181197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41955 (p : Pattern) (ha : d127463 p = 1) (hb : d181206 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52870 q = 1) (hb : d181198 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52870, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52870, d181198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52871 q = 1) (hb : d181199 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52871, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52871, d181199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d16656 q = 1) (hb : d127457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d127457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23315 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101310 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19009 q = 1) (hb : d127458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19009, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19009, d127458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101312 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127459 q = 1) (hb : d181200 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127459, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127459, d181200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127460 q = 1) (hb : d181201 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127460, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127460, d181201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127461 q = 1) (hb : d181202 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127461, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127461, d181202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14994 q = 1) (hb : d123119 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d123119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23313 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101299 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19001 q = 1) (hb : d123120 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19001, d123120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101301 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d123121 q = 1) (hb : d181194 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123121, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d123121, d181194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d123122 q = 1) (hb : d181195 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123122, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d123122, d181195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d19013 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d123131 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123131, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d123131, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d123132 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123132, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d123132, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d127462 q = 1) (hb : d181205 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127462, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127462, d181205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d127463 q = 1) (hb : d181206 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127463, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127463, d181206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41956 (p : Pattern) (ha : d127468 p = 1) (hb : d181214 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113454 q = 1) (hb : d181210 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113454, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113454, d181210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113455 q = 1) (hb : d181211 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113455, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113455, d181211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19013 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d123131 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123131, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123131, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d123132 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123132, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123132, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127467 q = 1) (hb : d181212 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127467, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127467, d181212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123133 q = 1) (hb : d181213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123133, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123133, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d127468 q = 1) (hb : d181214 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127468, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127468, d181214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41957 (p : Pattern) (ha : d127473 p = 1) (hb : d181224 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52692 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52875 q = 1) (hb : d181219 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52875, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52875, d181219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52876 q = 1) (hb : d181220 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52876, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52876, d181220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d1391 q = 1) (hb : d52879 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d52879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro151 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52702 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19034 q = 1) (hb : d52880 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19034, d52880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d52881 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52881, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d52881, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d52882 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52882, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d52882, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d52883 q = 1) (hb : d181223 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52883, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52883, d181223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15004 q = 1) (hb : d123129 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d123129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23303 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101321 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19013 q = 1) (hb : d123130 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19013, d123130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101323 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d123131 q = 1) (hb : d181203 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123131, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d123131, d181203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d123132 q = 1) (hb : d181204 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123132, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d123132, d181204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d123133 q = 1) (hb : d181213 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123133, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123133, d181213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d127473 q = 1) (hb : d181224 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127473, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127473, d181224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41958 (p : Pattern) (ha : d130676 p = 1) (hb : d181240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127464 q = 1) (hb : d181207 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127464, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41954 q ha hb
    | true =>
      simp only [d127464, d181207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41955 q ha hb
  have h2 (q : Pattern) (ha : d127465 q = 1) (hb : d181208 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127465, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127465, d181208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127466 q = 1) (hb : d181209 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127466, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127466, d181209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127469 q = 1) (hb : d181215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127469, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41955 q ha hb
    | true =>
      simp only [d127469, d181215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41956 q ha hb
  have h5 (q : Pattern) (ha : d127470 q = 1) (hb : d181216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127470, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127470, d181216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127471 q = 1) (hb : d181217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127471, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127471, d181217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127472 q = 1) (hb : d181218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127472, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127472, d181218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127474 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41955 q ha hb
    | true =>
      simp only [d127474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
  have h9 (q : Pattern) (ha : d127475 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127476 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127477 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127477, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
    | true =>
      simp only [d127477, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41953 q ha hb
  have h12 (q : Pattern) (ha : d127478 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127478, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127478, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127479 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127479, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127479, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127480 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127480, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127480, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127481 q = 1) (hb : d181239 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127481, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127481, d181239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d130676 q = 1) (hb : d181240 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130676, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130676, d181240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro41959 (p : Pattern) (ha : d130679 p = 1) (hb : d181245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127474 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41955 q ha hb
    | true =>
      simp only [d127474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
  have h2 (q : Pattern) (ha : d127475 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127476 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127477 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127477, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
    | true =>
      simp only [d127477, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41953 q ha hb
  have h5 (q : Pattern) (ha : d127478 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127478, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127478, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127479 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127479, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127479, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127480 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127480, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127480, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127485 q = 1) (hb : d181243 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127485, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127485, d181243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127486 q = 1) (hb : d181244 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127486, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127486, d181244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d130679 q = 1) (hb : d181245 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130679, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130679, d181245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41960 (p : Pattern) (ha : d130685 p = 1) (hb : d181251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130677 q = 1) (hb : d181241 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130677, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41958 q ha hb
    | true =>
      simp only [d130677, d181241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130678 q = 1) (hb : d181242 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130678, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130678, d181242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130680 q = 1) (hb : d181246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130680, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41959 q ha hb
    | true =>
      simp only [d130680, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130681 q = 1) (hb : d181247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130681, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130681, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130682 q = 1) (hb : d181248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130682, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130682, d181248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130683 q = 1) (hb : d181249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130683, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130683, d181249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130684 q = 1) (hb : d181250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130684, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130684, d181250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130685 q = 1) (hb : d181251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130685, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130685, d181251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41961 (p : Pattern) (ha : d123167 p = 1) (hb : d181253 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52881 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52881, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52881, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52882 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52882, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52882, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52888 q = 1) (hb : d181252 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52888, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52888, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19046 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19046, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123146 q = 1) (hb : d181231 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123146, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123146, d181231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123147 q = 1) (hb : d181232 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123147, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123147, d181232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123148 q = 1) (hb : d181233 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123148, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123148, d181233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123167 q = 1) (hb : d181253 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123167, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123167, d181253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41962 (p : Pattern) (ha : d130686 p = 1) (hb : d181259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127494 q = 1) (hb : d181254 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127494, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
    | true =>
      simp only [d127494, d181254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41961 q ha hb
  have h2 (q : Pattern) (ha : d127495 q = 1) (hb : d181255 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127495, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127495, d181255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127496 q = 1) (hb : d181256 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127496, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127496, d181256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127497 q = 1) (hb : d181257 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127497, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127497, d181257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127498 q = 1) (hb : d181258 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127498, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127498, d181258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130686 q = 1) (hb : d181259 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130686, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130686, d181259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro41963 (p : Pattern) (ha : d130692 p = 1) (hb : d181265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130680 q = 1) (hb : d181246 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130680, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41959 q ha hb
    | true =>
      simp only [d130680, d181246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130681 q = 1) (hb : d181247 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130681, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130681, d181247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130687 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130687, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41962 q ha hb
    | true =>
      simp only [d130687, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130688 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130688, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130688, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130689 q = 1) (hb : d181262 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130689, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130689, d181262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130690 q = 1) (hb : d181263 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130690, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130690, d181263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130691 q = 1) (hb : d181264 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130691, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130691, d181264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130692 q = 1) (hb : d181265 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130692, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130692, d181265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41964 (p : Pattern) (ha : d113482 p = 1) (hb : d181268 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52703 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d52881 q = 1) (hb : d181221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d52881, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d52881, d181221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d52882 q = 1) (hb : d181222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d52882, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d52882, d181222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d52888 q = 1) (hb : d181252 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d52888, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d52888, d181252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113482 q = 1) (hb : d181268 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113482, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113482, d181268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41965 (p : Pattern) (ha : d130707 p = 1) (hb : d181274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127474 q = 1) (hb : d181225 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41955 q ha hb
    | true =>
      simp only [d127474, d181225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
  have h2 (q : Pattern) (ha : d127475 q = 1) (hb : d181226 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127475, d181226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127476 q = 1) (hb : d181227 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127476, d181227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127477 q = 1) (hb : d181235 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127477, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
    | true =>
      simp only [d127477, d181235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41953 q ha hb
  have h5 (q : Pattern) (ha : d127478 q = 1) (hb : d181236 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127478, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127478, d181236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127479 q = 1) (hb : d181237 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127479, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127479, d181237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127480 q = 1) (hb : d181238 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127480, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127480, d181238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127521 q = 1) (hb : d181269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127521, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41957 q ha hb
    | true =>
      simp only [d127521, d181269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41964 q ha hb
  have h9 (q : Pattern) (ha : d127522 q = 1) (hb : d181270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127522, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127522, d181270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127523 q = 1) (hb : d181271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127523, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127523, d181271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127524 q = 1) (hb : d181272 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127524, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127524, d181272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127525 q = 1) (hb : d181273 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127525, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127525, d181273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d130707 q = 1) (hb : d181274 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130707, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130707, d181274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41966 (p : Pattern) (ha : d130713 p = 1) (hb : d181280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130708 q = 1) (hb : d181275 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130708, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41965 q ha hb
    | true =>
      simp only [d130708, d181275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130709 q = 1) (hb : d181276 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130709, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130709, d181276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130710 q = 1) (hb : d181277 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130710, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130710, d181277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130711 q = 1) (hb : d181278 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130711, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130711, d181278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130712 q = 1) (hb : d181279 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130712, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130712, d181279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130713 q = 1) (hb : d181280 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130713, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130713, d181280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41967 (p : Pattern) (ha : d130719 p = 1) (hb : d181286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130693 q = 1) (hb : d181266 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130693, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41960 q ha hb
    | true =>
      simp only [d130693, d181266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41963 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130706 q = 1) (hb : d181267 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130706, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130706, d181267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130714 q = 1) (hb : d181281 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130714, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41966 q ha hb
    | true =>
      simp only [d130714, d181281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130715 q = 1) (hb : d181282 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130715, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130715, d181282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130716 q = 1) (hb : d181283 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130716, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130716, d181283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130717 q = 1) (hb : d181284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130717, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130717, d181284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130718 q = 1) (hb : d181285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130718, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130718, d181285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130719 q = 1) (hb : d181286 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130719, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130719, d181286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41968 (p : Pattern) (ha : d130704 p = 1) (hb : d181291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130687 q = 1) (hb : d181260 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130687, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41962 q ha hb
    | true =>
      simp only [d130687, d181260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130688 q = 1) (hb : d181261 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130688, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130688, d181261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130701 q = 1) (hb : d181288 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130701, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130701, d181288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130702 q = 1) (hb : d181289 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130702, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130702, d181289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130703 q = 1) (hb : d181290 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130703, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130703, d181290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130704 q = 1) (hb : d181291 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130704, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130704, d181291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41969 (p : Pattern) (ha : d130726 p = 1) (hb : d181297 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130721 q = 1) (hb : d181292 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130721, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41968 q ha hb
    | true =>
      simp only [d130721, d181292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130722 q = 1) (hb : d181293 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130722, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130722, d181293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130723 q = 1) (hb : d181294 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130723, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130723, d181294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130724 q = 1) (hb : d181295 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130724, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130724, d181295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130725 q = 1) (hb : d181296 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130725, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130725, d181296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130726 q = 1) (hb : d181297 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130726, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130726, d181297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41970 (p : Pattern) (ha : d130732 p = 1) (hb : d181303 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130720 q = 1) (hb : d181287 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130720, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130720, d181287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41967 q ha hb
  have h2 (q : Pattern) (ha : d130727 q = 1) (hb : d181298 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130727, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130727, d181298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41969 q ha hb
  have h3 (q : Pattern) (ha : d130728 q = 1) (hb : d181299 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130728, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130728, d181299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130729 q = 1) (hb : d181300 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130729, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130729, d181300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130730 q = 1) (hb : d181301 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130730, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130730, d181301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130731 q = 1) (hb : d181302 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130731, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130731, d181302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130732 q = 1) (hb : d181303 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130732, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130732, d181303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41971 (p : Pattern) (ha : d130738 p = 1) (hb : d181309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130733 q = 1) (hb : d181304 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130733, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130733, d181304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41970 q ha hb
  have h2 (q : Pattern) (ha : d130734 q = 1) (hb : d181305 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130734, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130734, d181305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130735 q = 1) (hb : d181306 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130735, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130735, d181306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130736 q = 1) (hb : d181307 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130736, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130736, d181307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130737 q = 1) (hb : d181308 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130737, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130737, d181308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130738 q = 1) (hb : d181309 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130738, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130738, d181309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41972 (p : Pattern) (ha : d123456 p = 1) (hb : d181360 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69222 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76227 q = 1) (hb : d181354 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d76227, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76227, d181354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76228 q = 1) (hb : d181355 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d76228, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76228, d181355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d76229 q = 1) (hb : d181356 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d76229, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76229, d181356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19278 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123453 q = 1) (hb : d181357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123453, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123453, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123454 q = 1) (hb : d181358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123454, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123454, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123455 q = 1) (hb : d181359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123455, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123455, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123456 q = 1) (hb : d181360 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123456, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123456, d181360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41973 (p : Pattern) (ha : d127744 p = 1) (hb : d181323 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53107 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53181 q = 1) (hb : d181313 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53181, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53181, d181313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53182 q = 1) (hb : d181314 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53182, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53182, d181314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19226 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19226, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19226, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127740 q = 1) (hb : d181315 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127740, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127740, d181315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127741 q = 1) (hb : d181316 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127741, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127741, d181316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127742 q = 1) (hb : d181317 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127742, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127742, d181317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15380 q = 1) (hb : d123419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19230 q = 1) (hb : d123420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19230, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19230, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d123421 q = 1) (hb : d181318 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123421, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d123421, d181318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d123422 q = 1) (hb : d181319 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123422, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d123422, d181319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d19233 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d123428 q = 1) (hb : d181320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123428, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d123428, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d123429 q = 1) (hb : d181321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123429, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d123429, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d127743 q = 1) (hb : d181322 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127743, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127743, d181322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d127744 q = 1) (hb : d181323 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127744, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127744, d181323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41974 (p : Pattern) (ha : d127751 p = 1) (hb : d181332 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53185 q = 1) (hb : d181324 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53185, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53185, d181324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53186 q = 1) (hb : d181325 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53186, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53186, d181325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d17011 q = 1) (hb : d127745 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23343 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101501 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19241 q = 1) (hb : d127746 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19241, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19241, d127746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101503 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127747 q = 1) (hb : d181326 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127747, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127747, d181326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127748 q = 1) (hb : d181327 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127748, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127748, d181327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127749 q = 1) (hb : d181328 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127749, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127749, d181328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15387 q = 1) (hb : d123426 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23341 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101490 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19233 q = 1) (hb : d123427 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19233, d123427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101492 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d123428 q = 1) (hb : d181320 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123428, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d123428, d181320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d123429 q = 1) (hb : d181321 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123429, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d123429, d181321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d19245 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d123438 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123438, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d123438, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d123439 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123439, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d123439, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d127750 q = 1) (hb : d181331 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127750, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d127750, d181331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d127751 q = 1) (hb : d181332 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127751, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127751, d181332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41975 (p : Pattern) (ha : d127756 p = 1) (hb : d181340 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113710 q = 1) (hb : d181336 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113710, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113710, d181336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113711 q = 1) (hb : d181337 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113711, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113711, d181337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19245 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d123438 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123438, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123438, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d123439 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123439, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123439, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127755 q = 1) (hb : d181338 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127755, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127755, d181338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123440 q = 1) (hb : d181339 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123440, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123440, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d127756 q = 1) (hb : d181340 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127756, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127756, d181340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41976 (p : Pattern) (ha : d127766 p = 1) (hb : d181350 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53190 q = 1) (hb : d181345 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53190, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53190, d181345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53191 q = 1) (hb : d181346 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53191, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53191, d181346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d17027 q = 1) (hb : d127761 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23331 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101542 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19266 q = 1) (hb : d127762 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19266, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19266, d127762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101544 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d127763 q = 1) (hb : d181347 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d127763, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d127763, d181347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d127764 q = 1) (hb : d181348 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d127764, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d127764, d181348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d127765 q = 1) (hb : d181349 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d127765, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127765, d181349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15397 q = 1) (hb : d123436 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23330 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101512 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19245 q = 1) (hb : d123437 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19245, d123437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101514 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d123438 q = 1) (hb : d181329 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123438, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d123438, d181329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d123439 q = 1) (hb : d181330 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123439, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d123439, d181330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d123440 q = 1) (hb : d181339 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123440, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123440, d181339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d127766 q = 1) (hb : d181350 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d127766, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127766, d181350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41977 (p : Pattern) (ha : d130742 p = 1) (hb : d181366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127752 q = 1) (hb : d181333 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127752, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41973 q ha hb
    | true =>
      simp only [d127752, d181333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41974 q ha hb
  have h2 (q : Pattern) (ha : d127753 q = 1) (hb : d181334 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127753, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127753, d181334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127754 q = 1) (hb : d181335 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127754, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127754, d181335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127757 q = 1) (hb : d181341 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127757, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41974 q ha hb
    | true =>
      simp only [d127757, d181341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41975 q ha hb
  have h5 (q : Pattern) (ha : d127758 q = 1) (hb : d181342 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127758, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127758, d181342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127759 q = 1) (hb : d181343 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127759, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127759, d181343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127760 q = 1) (hb : d181344 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127760, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127760, d181344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127767 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127767, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41974 q ha hb
    | true =>
      simp only [d127767, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
  have h9 (q : Pattern) (ha : d127768 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127768, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127768, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127769 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127769, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127769, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127770 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127770, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
    | true =>
      simp only [d127770, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41972 q ha hb
  have h12 (q : Pattern) (ha : d127771 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127771, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127771, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127772 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127772, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127772, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d127773 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127773, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127773, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d127774 q = 1) (hb : d181365 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127774, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127774, d181365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d130742 q = 1) (hb : d181366 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130742, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130742, d181366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro41978 (p : Pattern) (ha : d130745 p = 1) (hb : d181371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127767 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127767, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41974 q ha hb
    | true =>
      simp only [d127767, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
  have h2 (q : Pattern) (ha : d127768 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127768, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127768, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127769 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127769, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127769, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127770 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127770, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
    | true =>
      simp only [d127770, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41972 q ha hb
  have h5 (q : Pattern) (ha : d127771 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127771, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127771, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127772 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127772, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127772, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127773 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127773, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127773, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127778 q = 1) (hb : d181369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127778, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127778, d181369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d127779 q = 1) (hb : d181370 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127779, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127779, d181370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d130745 q = 1) (hb : d181371 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130745, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130745, d181371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41979 (p : Pattern) (ha : d130751 p = 1) (hb : d181377 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130743 q = 1) (hb : d181367 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130743, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41977 q ha hb
    | true =>
      simp only [d130743, d181367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130744 q = 1) (hb : d181368 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130744, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130744, d181368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130746 q = 1) (hb : d181372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130746, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41978 q ha hb
    | true =>
      simp only [d130746, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130747 q = 1) (hb : d181373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130747, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130747, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130748 q = 1) (hb : d181374 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130748, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130748, d181374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130749 q = 1) (hb : d181375 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130749, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130749, d181375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130750 q = 1) (hb : d181376 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130750, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130750, d181376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130751 q = 1) (hb : d181377 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130751, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130751, d181377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41980 (p : Pattern) (ha : d123474 p = 1) (hb : d181381 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53196 q = 1) (hb : d181378 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53196, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53196, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53197 q = 1) (hb : d181379 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53197, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53197, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53203 q = 1) (hb : d181380 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53203, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53203, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19278 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19278, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123453 q = 1) (hb : d181357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123453, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123453, d181357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123454 q = 1) (hb : d181358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123454, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123454, d181358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123455 q = 1) (hb : d181359 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123455, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123455, d181359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123474 q = 1) (hb : d181381 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123474, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123474, d181381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41981 (p : Pattern) (ha : d130752 p = 1) (hb : d181387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127787 q = 1) (hb : d181382 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127787, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
    | true =>
      simp only [d127787, d181382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41980 q ha hb
  have h2 (q : Pattern) (ha : d127788 q = 1) (hb : d181383 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127788, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127788, d181383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127789 q = 1) (hb : d181384 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127789, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127789, d181384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127790 q = 1) (hb : d181385 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127790, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127790, d181385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d127791 q = 1) (hb : d181386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127791, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d127791, d181386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130752 q = 1) (hb : d181387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130752, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130752, d181387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro41982 (p : Pattern) (ha : d130758 p = 1) (hb : d181393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130746 q = 1) (hb : d181372 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130746, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41978 q ha hb
    | true =>
      simp only [d130746, d181372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130747 q = 1) (hb : d181373 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130747, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130747, d181373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130753 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130753, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41981 q ha hb
    | true =>
      simp only [d130753, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130754 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130754, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130754, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130755 q = 1) (hb : d181390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130755, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130755, d181390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130756 q = 1) (hb : d181391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130756, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130756, d181391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130757 q = 1) (hb : d181392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130757, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130757, d181392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130758 q = 1) (hb : d181393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130758, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130758, d181393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41983 (p : Pattern) (ha : d113738 p = 1) (hb : d181396 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53196 q = 1) (hb : d181378 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53196, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53196, d181378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53197 q = 1) (hb : d181379 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53197, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53197, d181379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53203 q = 1) (hb : d181380 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53203, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53203, d181380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113738 q = 1) (hb : d181396 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113738, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113738, d181396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41984 (p : Pattern) (ha : d130773 p = 1) (hb : d181402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127767 q = 1) (hb : d181351 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127767, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41974 q ha hb
    | true =>
      simp only [d127767, d181351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
  have h2 (q : Pattern) (ha : d127768 q = 1) (hb : d181352 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127768, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127768, d181352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127769 q = 1) (hb : d181353 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127769, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127769, d181353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127770 q = 1) (hb : d181361 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127770, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
    | true =>
      simp only [d127770, d181361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41972 q ha hb
  have h5 (q : Pattern) (ha : d127771 q = 1) (hb : d181362 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127771, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127771, d181362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127772 q = 1) (hb : d181363 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127772, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127772, d181363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127773 q = 1) (hb : d181364 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127773, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127773, d181364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127814 q = 1) (hb : d181397 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d127814, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41976 q ha hb
    | true =>
      simp only [d127814, d181397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41983 q ha hb
  have h9 (q : Pattern) (ha : d127815 q = 1) (hb : d181398 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d127815, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127815, d181398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127816 q = 1) (hb : d181399 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d127816, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127816, d181399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d127817 q = 1) (hb : d181400 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d127817, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127817, d181400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d127818 q = 1) (hb : d181401 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127818, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127818, d181401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d130773 q = 1) (hb : d181402 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130773, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130773, d181402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro41985 (p : Pattern) (ha : d130779 p = 1) (hb : d181408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130774 q = 1) (hb : d181403 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130774, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41984 q ha hb
    | true =>
      simp only [d130774, d181403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130775 q = 1) (hb : d181404 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130775, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130775, d181404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130776 q = 1) (hb : d181405 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130776, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130776, d181405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130777 q = 1) (hb : d181406 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130777, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130777, d181406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130778 q = 1) (hb : d181407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130778, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130778, d181407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130779 q = 1) (hb : d181408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130779, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130779, d181408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41986 (p : Pattern) (ha : d130785 p = 1) (hb : d181414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130759 q = 1) (hb : d181394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130759, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41979 q ha hb
    | true =>
      simp only [d130759, d181394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41982 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130772 q = 1) (hb : d181395 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130772, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130772, d181395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130780 q = 1) (hb : d181409 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130780, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41985 q ha hb
    | true =>
      simp only [d130780, d181409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130781 q = 1) (hb : d181410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130781, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130781, d181410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130782 q = 1) (hb : d181411 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130782, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130782, d181411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130783 q = 1) (hb : d181412 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130783, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130783, d181412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130784 q = 1) (hb : d181413 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130784, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130784, d181413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130785 q = 1) (hb : d181414 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130785, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130785, d181414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro41987 (p : Pattern) (ha : d130770 p = 1) (hb : d181419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130753 q = 1) (hb : d181388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130753, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41981 q ha hb
    | true =>
      simp only [d130753, d181388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130754 q = 1) (hb : d181389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130754, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130754, d181389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130767 q = 1) (hb : d181416 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130767, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130767, d181416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130768 q = 1) (hb : d181417 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130768, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130768, d181417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130769 q = 1) (hb : d181418 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130769, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130769, d181418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130770 q = 1) (hb : d181419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130770, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130770, d181419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro41988 (p : Pattern) (ha : d130792 p = 1) (hb : d181425 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130787 q = 1) (hb : d181420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130787, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41987 q ha hb
    | true =>
      simp only [d130787, d181420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130788 q = 1) (hb : d181421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130788, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130788, d181421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130789 q = 1) (hb : d181422 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130789, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130789, d181422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130790 q = 1) (hb : d181423 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130790, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130790, d181423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130791 q = 1) (hb : d181424 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130791, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130791, d181424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130792 q = 1) (hb : d181425 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130792, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130792, d181425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41989 (p : Pattern) (ha : d130798 p = 1) (hb : d181431 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130786 q = 1) (hb : d181415 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130786, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130786, d181415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41986 q ha hb
  have h2 (q : Pattern) (ha : d130793 q = 1) (hb : d181426 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130793, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130793, d181426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41988 q ha hb
  have h3 (q : Pattern) (ha : d130794 q = 1) (hb : d181427 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130794, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130794, d181427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130795 q = 1) (hb : d181428 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130795, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130795, d181428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130796 q = 1) (hb : d181429 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130796, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130796, d181429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130797 q = 1) (hb : d181430 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130797, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130797, d181430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130798 q = 1) (hb : d181431 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130798, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130798, d181431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro41990 (p : Pattern) (ha : d130804 p = 1) (hb : d181437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130799 q = 1) (hb : d181432 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130799, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130799, d181432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41989 q ha hb
  have h2 (q : Pattern) (ha : d130800 q = 1) (hb : d181433 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130800, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130800, d181433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130801 q = 1) (hb : d181434 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130801, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130801, d181434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130802 q = 1) (hb : d181435 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130802, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130802, d181435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130803 q = 1) (hb : d181436 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130803, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130803, d181436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130804 q = 1) (hb : d181437 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130804, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130804, d181437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro41991 (p : Pattern) (ha : d123748 p = 1) (hb : d181484 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d76363 q = 1) (hb : d181478 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d76363, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d76363, d181478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d76364 q = 1) (hb : d181479 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d76364, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d76364, d181479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d76365 q = 1) (hb : d181480 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d76365, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76365, d181480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19510 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123745 q = 1) (hb : d181481 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123745, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123745, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123746 q = 1) (hb : d181482 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123746, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123746, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123747 q = 1) (hb : d181483 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123747, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123747, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123748 q = 1) (hb : d181484 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123748, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123748, d181484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41992 (p : Pattern) (ha : d128037 p = 1) (hb : d181450 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53424 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53498 q = 1) (hb : d181442 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53498, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53498, d181442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53499 q = 1) (hb : d181443 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53499, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53499, d181443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19465 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19465, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19465, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d128033 q = 1) (hb : d181444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128033, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128033, d181444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d128034 q = 1) (hb : d181445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128034, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128034, d181445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128035 q = 1) (hb : d181446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128035, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128035, d181446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19469 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d113967 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113967, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d113967, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d113968 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113968, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d113968, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d128036 q = 1) (hb : d181449 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128036, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128036, d181449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128037 q = 1) (hb : d181450 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128037, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128037, d181450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41993 (p : Pattern) (ha : d128044 p = 1) (hb : d181459 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53502 q = 1) (hb : d181451 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53502, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53502, d181451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53503 q = 1) (hb : d181452 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53503, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53503, d181452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19477 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19477, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19477, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d128040 q = 1) (hb : d181453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128040, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128040, d181453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d128041 q = 1) (hb : d181454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128041, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128041, d181454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128042 q = 1) (hb : d181455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128042, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128042, d181455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19469 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19469, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d113967 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113967, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d113967, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d113968 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113968, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d113968, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d19481 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d123730 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123730, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d123730, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d123731 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123731, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d123731, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d128043 q = 1) (hb : d181458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128043, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128043, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128044 q = 1) (hb : d181459 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128044, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128044, d181459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro41994 (p : Pattern) (ha : d128048 p = 1) (hb : d181464 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113967 q = 1) (hb : d181447 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d113967, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113967, d181447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113968 q = 1) (hb : d181448 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d113968, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113968, d181448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19481 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d123730 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123730, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d123730, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d123731 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123731, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d123731, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128043 q = 1) (hb : d181458 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128043, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128043, d181458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d123732 q = 1) (hb : d181463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123732, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123732, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128048 q = 1) (hb : d181464 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128048, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128048, d181464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro41995 (p : Pattern) (ha : d128058 p = 1) (hb : d181474 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53507 q = 1) (hb : d181469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53507, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53507, d181469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53508 q = 1) (hb : d181470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53508, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53508, d181470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d17391 q = 1) (hb : d128053 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23359 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d101712 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d19498 q = 1) (hb : d128054 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19498, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19498, d128054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101714 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d128055 q = 1) (hb : d181471 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d128055, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d128055, d181471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d128056 q = 1) (hb : d181472 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d128056, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128056, d181472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d128057 q = 1) (hb : d181473 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d128057, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128057, d181473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15775 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23358 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d19481 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19481, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d123730 q = 1) (hb : d181456 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123730, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
    | true =>
      simp only [d123730, d181456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d123731 q = 1) (hb : d181457 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123731, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d123731, d181457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d123732 q = 1) (hb : d181463 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123732, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d123732, d181463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128058 q = 1) (hb : d181474 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d128058, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128058, d181474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro41996 (p : Pattern) (ha : d130809 p = 1) (hb : d181490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128045 q = 1) (hb : d181460 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128045, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41992 q ha hb
    | true =>
      simp only [d128045, d181460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41993 q ha hb
  have h2 (q : Pattern) (ha : d128046 q = 1) (hb : d181461 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128046, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128046, d181461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128047 q = 1) (hb : d181462 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128047, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128047, d181462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128049 q = 1) (hb : d181465 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128049, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41993 q ha hb
    | true =>
      simp only [d128049, d181465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41994 q ha hb
  have h5 (q : Pattern) (ha : d128050 q = 1) (hb : d181466 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128050, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128050, d181466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128051 q = 1) (hb : d181467 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128051, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128051, d181467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128052 q = 1) (hb : d181468 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128052, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128052, d181468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128059 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128059, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41993 q ha hb
    | true =>
      simp only [d128059, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41995 q ha hb
  have h9 (q : Pattern) (ha : d128060 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128060, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128060, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128061 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128061, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128061, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128062 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128062, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41995 q ha hb
    | true =>
      simp only [d128062, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41991 q ha hb
  have h12 (q : Pattern) (ha : d128063 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128063, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128063, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128064 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128064, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128064, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128065 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128065, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128065, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128066 q = 1) (hb : d181489 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128066, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128066, d181489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d130809 q = 1) (hb : d181490 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130809, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130809, d181490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro41997 (p : Pattern) (ha : d130812 p = 1) (hb : d181495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128059 q = 1) (hb : d181475 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128059, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41993 q ha hb
    | true =>
      simp only [d128059, d181475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41995 q ha hb
  have h2 (q : Pattern) (ha : d128060 q = 1) (hb : d181476 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128060, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128060, d181476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128061 q = 1) (hb : d181477 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128061, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128061, d181477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128062 q = 1) (hb : d181485 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d128062, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41995 q ha hb
    | true =>
      simp only [d128062, d181485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41991 q ha hb
  have h5 (q : Pattern) (ha : d128063 q = 1) (hb : d181486 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d128063, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128063, d181486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128064 q = 1) (hb : d181487 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d128064, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128064, d181487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128065 q = 1) (hb : d181488 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128065, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128065, d181488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128070 q = 1) (hb : d181493 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d128070, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128070, d181493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d128071 q = 1) (hb : d181494 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128071, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128071, d181494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d130812 q = 1) (hb : d181495 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130812, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d130812, d181495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro41998 (p : Pattern) (ha : d130818 p = 1) (hb : d181501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130810 q = 1) (hb : d181491 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130810, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41996 q ha hb
    | true =>
      simp only [d130810, d181491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130811 q = 1) (hb : d181492 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130811, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130811, d181492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130813 q = 1) (hb : d181496 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130813, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro41997 q ha hb
    | true =>
      simp only [d130813, d181496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130814 q = 1) (hb : d181497 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130814, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130814, d181497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130815 q = 1) (hb : d181498 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130815, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130815, d181498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130816 q = 1) (hb : d181499 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130816, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130816, d181499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130817 q = 1) (hb : d181500 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130817, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130817, d181500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130818 q = 1) (hb : d181501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130818, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130818, d181501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro41999 (p : Pattern) (ha : d123766 p = 1) (hb : d181505 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53513 q = 1) (hb : d181502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d53513, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d53513, d181502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d53514 q = 1) (hb : d181503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d53514, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53514, d181503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d53520 q = 1) (hb : d181504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d53520, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53520, d181504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d19510 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19510, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d123745 q = 1) (hb : d181481 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d123745, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d123745, d181481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d123746 q = 1) (hb : d181482 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d123746, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d123746, d181482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d123747 q = 1) (hb : d181483 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d123747, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d123747, d181483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d123766 q = 1) (hb : d181505 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d123766, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d123766, d181505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
