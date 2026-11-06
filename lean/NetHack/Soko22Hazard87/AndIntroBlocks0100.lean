import NetHack.Soko22Hazard87.AndIntroBlocks0099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro25000 (p : Pattern) (ha : d11615 p = 1) (hb : d52929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11560 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24999 q ha hb
    | true =>
      simp only [d11560, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11561 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11612 q = 1) (hb : d52926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11612, d52926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11612, d52926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11613 q = 1) (hb : d52927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11613, d52927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11613, d52927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11614 q = 1) (hb : d52928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11614, d52928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11614, d52928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11615 q = 1) (hb : d52929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11615, d52929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11615, d52929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25001 (p : Pattern) (ha : d11621 p = 1) (hb : d52944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11616 q = 1) (hb : d52939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11616, d52939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25000 q ha hb
    | true =>
      simp only [d11616, d52939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11617 q = 1) (hb : d52940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11617, d52940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11617, d52940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11618 q = 1) (hb : d52941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11618, d52941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11618, d52941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11619 q = 1) (hb : d52942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11619, d52942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11619, d52942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11620 q = 1) (hb : d52943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11620, d52943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11620, d52943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11621 q = 1) (hb : d52944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11621, d52944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11621, d52944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25002 (p : Pattern) (ha : d84093 p = 1) (hb : d111004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11366 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11367 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11368 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52722 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11369 q = 1) (hb : d52723 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro153 q ha hb
    | true =>
      simp only [d11369, d52723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11370 q = 1) (hb : d52724 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11370, d52724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11371 q = 1) (hb : d52725 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11371, d52725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11372 q = 1) (hb : d52726 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11372, d52726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84092 q = 1) (hb : d111003 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84092, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84092, d111003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84093 q = 1) (hb : d111004 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84093, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84093, d111004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25003 (p : Pattern) (ha : d84099 p = 1) (hb : d111010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84098 q = 1) (hb : d111009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84098, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84098, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84099 q = 1) (hb : d111010 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84099, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84099, d111010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25004 (p : Pattern) (ha : d84105 p = 1) (hb : d111016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25003 q ha hb
    | true =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84105 q = 1) (hb : d111016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84105, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84105, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25005 (p : Pattern) (ha : d84108 p = 1) (hb : d111019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84098 q = 1) (hb : d111009 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84098, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84098, d111009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84108 q = 1) (hb : d111019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84108, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84108, d111019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25006 (p : Pattern) (ha : d84114 p = 1) (hb : d111025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25003 q ha hb
    | true =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84109 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25005 q ha hb
    | true =>
      simp only [d84109, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q hb ha
  have h7 (q : Pattern) (ha : d84110 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84110, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84110, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84111 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84111, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84111, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84112 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84112, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84112, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84113 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84113, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84113, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84114 q = 1) (hb : d111025 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84114, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84114, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25007 (p : Pattern) (ha : d11412 p = 1) (hb : d52766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d52741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d52765 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d52765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d52765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11412 q = 1) (hb : d52766 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11412, d52766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11412, d52766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25008 (p : Pattern) (ha : d11422 p = 1) (hb : d52776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d52774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d52774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d52774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d52775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d52775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d52775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11422 q = 1) (hb : d52776 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11422, d52776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11422, d52776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25009 (p : Pattern) (ha : d84119 p = 1) (hb : d111030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84118 q = 1) (hb : d111029 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84118, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84118, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84119 q = 1) (hb : d111030 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84119, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84119, d111030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25010 (p : Pattern) (ha : d84126 p = 1) (hb : d111037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84124 q = 1) (hb : d111035 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84124, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84124, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84125 q = 1) (hb : d111036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84125, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84125, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84126 q = 1) (hb : d111037 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84126, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84126, d111037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25011 (p : Pattern) (ha : d84131 p = 1) (hb : d111042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52707 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11426 q = 1) (hb : d52797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11426, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro175 q ha hb
    | true =>
      simp only [d11426, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11427 q = 1) (hb : d52798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11427, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11427, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11428 q = 1) (hb : d52799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11428, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11428, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52709 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11366 q = 1) (hb : d52710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
    | true =>
      simp only [d11366, d52710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11367 q = 1) (hb : d52711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11367, d52711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11368 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11368, d52712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11429 q = 1) (hb : d52800 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11429, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84130 q = 1) (hb : d111041 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84130, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84130, d111041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84131 q = 1) (hb : d111042 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84131, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84131, d111042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25012 (p : Pattern) (ha : d84137 p = 1) (hb : d111048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84132 q = 1) (hb : d111043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84132, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25011 q ha hb
    | true =>
      simp only [d84132, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84133 q = 1) (hb : d111044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84133, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84133, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d111045 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84134, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d111046 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d111047 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84137 q = 1) (hb : d111048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84137, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84137, d111048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25013 (p : Pattern) (ha : d84143 p = 1) (hb : d111054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84140 q = 1) (hb : d111051 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84140, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84140, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84141 q = 1) (hb : d111052 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84141, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84141, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84142 q = 1) (hb : d111053 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84142, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84142, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84143 q = 1) (hb : d111054 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84143, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84143, d111054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25014 (p : Pattern) (ha : d84149 p = 1) (hb : d111060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84120 q = 1) (hb : d111031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84120, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25009 q ha hb
    | true =>
      simp only [d84120, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25007 q hb ha
  have h2 (q : Pattern) (ha : d84121 q = 1) (hb : d111032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84121, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84121, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84122 q = 1) (hb : d111033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84122, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84122, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84123 q = 1) (hb : d111034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84123, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84123, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84127 q = 1) (hb : d111038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84127, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25010 q ha hb
    | true =>
      simp only [d84127, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25008 q hb ha
  have h6 (q : Pattern) (ha : d84128 q = 1) (hb : d111039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84128, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84128, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84129 q = 1) (hb : d111040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84129, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84129, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d111049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25012 q ha hb
    | true =>
      simp only [d84138, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25003 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d111050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84144 q = 1) (hb : d111055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84144, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25013 q ha hb
    | true =>
      simp only [d84144, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84145 q = 1) (hb : d111056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84145, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84145, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d111057 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d111058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84147, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d111059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84148, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84149 q = 1) (hb : d111060 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84149, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84149, d111060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro25015 (p : Pattern) (ha : d11484 p = 1) (hb : d52818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11387 q = 1) (hb : d52741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11387, d52741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11411 q = 1) (hb : d52765 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d52765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11411, d52765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11484 q = 1) (hb : d52818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11484, d52818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11484, d52818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25016 (p : Pattern) (ha : d11490 p = 1) (hb : d52824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11386 q = 1) (hb : d52740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11386, d52740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11420 q = 1) (hb : d52774 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d52774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11420, d52774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11421 q = 1) (hb : d52775 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d52775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11421, d52775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11490 q = 1) (hb : d52824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11490, d52824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11490, d52824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25017 (p : Pattern) (ha : d84150 p = 1) (hb : d111061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d111008 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d111008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84118 q = 1) (hb : d111029 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84118, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84118, d111029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84150 q = 1) (hb : d111061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84150, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84150, d111061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25018 (p : Pattern) (ha : d84155 p = 1) (hb : d111066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11380 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24994 q ha hb
    | true =>
      simp only [d11380, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11381 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11381, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d111007 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d111007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84124 q = 1) (hb : d111035 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84124, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84124, d111035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84125 q = 1) (hb : d111036 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84125, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84125, d111036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84155 q = 1) (hb : d111066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84155, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84155, d111066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25019 (p : Pattern) (ha : d84159 p = 1) (hb : d111070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84132 q = 1) (hb : d111043 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84132, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25011 q ha hb
    | true =>
      simp only [d84132, d111043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84133 q = 1) (hb : d111044 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84133, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84133, d111044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d111045 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84134, d111045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d111046 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d111046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d111047 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d111047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84159 q = 1) (hb : d111070 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84159, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84159, d111070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25020 (p : Pattern) (ha : d84162 p = 1) (hb : d111073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d111005 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25002 q ha hb
    | true =>
      simp only [d84094, d111005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d111006 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d111006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84140 q = 1) (hb : d111051 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84140, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84140, d111051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84141 q = 1) (hb : d111052 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84141, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84141, d111052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84142 q = 1) (hb : d111053 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84142, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84142, d111053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84162 q = 1) (hb : d111073 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84162, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84162, d111073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25021 (p : Pattern) (ha : d84168 p = 1) (hb : d111079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84120 q = 1) (hb : d111031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84120, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25009 q ha hb
    | true =>
      simp only [d84120, d111031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25007 q hb ha
  have h2 (q : Pattern) (ha : d84121 q = 1) (hb : d111032 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84121, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84121, d111032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84122 q = 1) (hb : d111033 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84122, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84122, d111033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84123 q = 1) (hb : d111034 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84123, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84123, d111034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84127 q = 1) (hb : d111038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84127, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25010 q ha hb
    | true =>
      simp only [d84127, d111038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25008 q hb ha
  have h6 (q : Pattern) (ha : d84128 q = 1) (hb : d111039 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84128, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84128, d111039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84129 q = 1) (hb : d111040 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84129, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84129, d111040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d111049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25012 q ha hb
    | true =>
      simp only [d84138, d111049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25003 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d111050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d111050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84144 q = 1) (hb : d111055 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84144, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25013 q ha hb
    | true =>
      simp only [d84144, d111055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84145 q = 1) (hb : d111056 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84145, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84145, d111056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d111057 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d111057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d111058 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84147, d111058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d111059 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84148, d111059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84151 q = 1) (hb : d111062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84151, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25017 q ha hb
    | true =>
      simp only [d84151, d111062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25015 q hb ha
  have h17 (q : Pattern) (ha : d84152 q = 1) (hb : d111063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84152, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84152, d111063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84153 q = 1) (hb : d111064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84153, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84153, d111064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84154 q = 1) (hb : d111065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84154, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84154, d111065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84156 q = 1) (hb : d111067 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84156, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25018 q ha hb
    | true =>
      simp only [d84156, d111067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25016 q hb ha
  have h21 (q : Pattern) (ha : d84157 q = 1) (hb : d111068 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84157, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84157, d111068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84158 q = 1) (hb : d111069 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84158, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84158, d111069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84160 q = 1) (hb : d111071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25019 q ha hb
    | true =>
      simp only [d84160, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25005 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84161 q = 1) (hb : d111072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84161, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84163 q = 1) (hb : d111074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84163, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25020 q ha hb
    | true =>
      simp only [d84163, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84164 q = 1) (hb : d111075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84164, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84164, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84165 q = 1) (hb : d111076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84165, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84166 q = 1) (hb : d111077 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84166, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84166, d111077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84167 q = 1) (hb : d111078 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84167, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84167, d111078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84168 q = 1) (hb : d111079 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84168, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84168, d111079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro25022 (p : Pattern) (ha : d84170 p = 1) (hb : d111081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25003 q ha hb
    | true =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11508 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q ha hb
    | true =>
      simp only [d11508, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11509 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11509, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11510 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11510, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11511 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11511, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11512 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11512, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84170 q = 1) (hb : d111081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84170, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84170, d111081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro25023 (p : Pattern) (ha : d84177 p = 1) (hb : d111088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84160 q = 1) (hb : d111071 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25019 q ha hb
    | true =>
      simp only [d84160, d111071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25005 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84161 q = 1) (hb : d111072 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84161, d111072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84163 q = 1) (hb : d111074 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84163, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25020 q ha hb
    | true =>
      simp only [d84163, d111074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84164 q = 1) (hb : d111075 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84164, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84164, d111075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84165 q = 1) (hb : d111076 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84165, d111076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84175 q = 1) (hb : d111086 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84175, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84175, d111086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84176 q = 1) (hb : d111087 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84176, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84176, d111087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84177 q = 1) (hb : d111088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d111088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25024 (p : Pattern) (ha : d84184 p = 1) (hb : d111095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11534 q = 1) (hb : d52885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11534, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro179 q ha hb
    | true =>
      simp only [d11534, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11535 q = 1) (hb : d52886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11535, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11535, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11536 q = 1) (hb : d52887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11536, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11536, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11537 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11538 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11539 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11540 q = 1) (hb : d52893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11540, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84183 q = 1) (hb : d111094 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84183, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84183, d111094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84184 q = 1) (hb : d111095 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84184, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84184, d111095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25025 (p : Pattern) (ha : d84188 p = 1) (hb : d111099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52889 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11537 q = 1) (hb : d52890 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
    | true =>
      simp only [d11537, d52890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11538 q = 1) (hb : d52891 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11538, d52891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11539 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11539, d52892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52899 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11541 q = 1) (hb : d52900 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro167 q ha hb
    | true =>
      simp only [d11541, d52900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11542 q = 1) (hb : d52901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11542, d52901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11543 q = 1) (hb : d52902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11543, d52902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11544 q = 1) (hb : d52903 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11544, d52903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84187 q = 1) (hb : d111098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84187, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84187, d111098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84188 q = 1) (hb : d111099 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84188, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84188, d111099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25026 (p : Pattern) (ha : d84194 p = 1) (hb : d111105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84185 q = 1) (hb : d111096 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84185, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25024 q ha hb
    | true =>
      simp only [d84185, d111096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84186 q = 1) (hb : d111097 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84186, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84186, d111097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84189 q = 1) (hb : d111100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25025 q ha hb
    | true =>
      simp only [d84189, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84190 q = 1) (hb : d111101 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84191 q = 1) (hb : d111102 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84191, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84191, d111102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84192 q = 1) (hb : d111103 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84192, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84192, d111103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84193 q = 1) (hb : d111104 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84193, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84193, d111104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84194 q = 1) (hb : d111105 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84194, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84194, d111105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25027 (p : Pattern) (ha : d84198 p = 1) (hb : d111109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84189 q = 1) (hb : d111100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25025 q ha hb
    | true =>
      simp only [d84189, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84190 q = 1) (hb : d111101 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11560 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24999 q ha hb
    | true =>
      simp only [d11560, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11561 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11561, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84195 q = 1) (hb : d111106 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84195, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84195, d111106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84196 q = 1) (hb : d111107 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84196, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84196, d111107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84197 q = 1) (hb : d111108 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84197, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84197, d111108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84198 q = 1) (hb : d111109 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84198, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84198, d111109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25028 (p : Pattern) (ha : d84205 p = 1) (hb : d111115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84189 q = 1) (hb : d111100 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25025 q ha hb
    | true =>
      simp only [d84189, d111100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84190 q = 1) (hb : d111101 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d111101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84202 q = 1) (hb : d111112 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84202, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84202, d111112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84203 q = 1) (hb : d111113 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84203, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84203, d111113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84204 q = 1) (hb : d111114 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84204, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84204, d111114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84205 q = 1) (hb : d111115 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84205, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84205, d111115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25029 (p : Pattern) (ha : d84211 p = 1) (hb : d111121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84199 q = 1) (hb : d111110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84199, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25026 q ha hb
    | true =>
      simp only [d84199, d111110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25027 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d111111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84201, d111111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84206 q = 1) (hb : d111116 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84206, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25028 q ha hb
    | true =>
      simp only [d84206, d111116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84207 q = 1) (hb : d111117 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84207, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84207, d111117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84208 q = 1) (hb : d111118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d111118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84209 q = 1) (hb : d111119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d111119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84210 q = 1) (hb : d111120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d111120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84211 q = 1) (hb : d111121 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d111121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25030 (p : Pattern) (ha : d84217 p = 1) (hb : d111127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84106 q = 1) (hb : d111017 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84106, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84106, d111017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25004 q ha hb
  have h2 (q : Pattern) (ha : d84107 q = 1) (hb : d111018 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84107, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84107, d111018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84115 q = 1) (hb : d111026 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84115, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25004 q ha hb
    | true =>
      simp only [d84115, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25006 q ha hb
  have h4 (q : Pattern) (ha : d84116 q = 1) (hb : d111027 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84116, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84116, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84117 q = 1) (hb : d111028 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84117, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84117, d111028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84169 q = 1) (hb : d111080 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84169, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25014 q ha hb
    | true =>
      simp only [d84169, d111080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25021 q ha hb
  have h7 (q : Pattern) (ha : d84171 q = 1) (hb : d111082 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84171, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25022 q ha hb
    | true =>
      simp only [d84171, d111082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24997 q hb ha
  have h8 (q : Pattern) (ha : d84172 q = 1) (hb : d111083 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84172, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84172, d111083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84173 q = 1) (hb : d111084 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84173, d111084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84174 q = 1) (hb : d111085 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84174, d111085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84178 q = 1) (hb : d111089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84178, d111089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25023 q ha hb
  have h12 (q : Pattern) (ha : d11529 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11529, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24998 q ha hb
  have h13 (q : Pattern) (ha : d84179 q = 1) (hb : d111090 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84179, d111090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84180 q = 1) (hb : d111091 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84180, d111091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84181 q = 1) (hb : d111092 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84181, d111092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84182 q = 1) (hb : d111093 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84182, d111093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84212 q = 1) (hb : d111122 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84212, d111122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25029 q ha hb
  have h18 (q : Pattern) (ha : d11622 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11622, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25001 q ha hb
  have h19 (q : Pattern) (ha : d84213 q = 1) (hb : d111123 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84213, d111123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84214 q = 1) (hb : d111124 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84214, d111124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84215 q = 1) (hb : d111125 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84215, d111125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84216 q = 1) (hb : d111126 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84216, d111126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84217 q = 1) (hb : d111127 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84217, d111127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25031 (p : Pattern) (ha : d84223 p = 1) (hb : d111133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d111128 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d111128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25030 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d111129 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d111129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d111130 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d111130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d111131 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d111131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d111132 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d111132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d111133 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d111133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25032 (p : Pattern) (ha : d11650 p = 1) (hb : d53054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11640 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11641 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11642 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11644 q = 1) (hb : d53048 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11644, d53048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11649 q = 1) (hb : d53053 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11649, d53053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11649, d53053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11650 q = 1) (hb : d53054 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11650, d53054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11650, d53054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25033 (p : Pattern) (ha : d11660 p = 1) (hb : d53064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d53062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d53063 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d53063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d53063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11660 q = 1) (hb : d53064 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11660, d53064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11660, d53064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25034 (p : Pattern) (ha : d11670 p = 1) (hb : d53074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d53062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11659 q = 1) (hb : d53063 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d53063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11659, d53063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11670 q = 1) (hb : d53074 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11670, d53074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11670, d53074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25035 (p : Pattern) (ha : d11790 p = 1) (hb : d53164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11779 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
    | true =>
      simp only [d11779, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11780 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11781 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11781, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11782 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11783 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11785 q = 1) (hb : d53159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d53159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q ha hb
    | true =>
      simp only [d11785, d53159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11786 q = 1) (hb : d53160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d53160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d53160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11787 q = 1) (hb : d53161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d53161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11787, d53161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11788 q = 1) (hb : d53162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d53162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d53162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11789 q = 1) (hb : d53163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d53163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d53163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11790 q = 1) (hb : d53164 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11790, d53164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11790, d53164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25036 (p : Pattern) (ha : d11799 p = 1) (hb : d53173 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11785 q = 1) (hb : d53159 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d53159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q ha hb
    | true =>
      simp only [d11785, d53159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11786 q = 1) (hb : d53160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d53160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11786, d53160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11787 q = 1) (hb : d53161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d53161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11787, d53161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11788 q = 1) (hb : d53162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d53162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11788, d53162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11789 q = 1) (hb : d53163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d53163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11789, d53163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11799 q = 1) (hb : d53173 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11799, d53173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11799, d53173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25037 (p : Pattern) (ha : d11830 p = 1) (hb : d53233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11812 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11813 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11814 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11820 q = 1) (hb : d53223 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11820, d53223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11829 q = 1) (hb : d53232 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11829, d53232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11829, d53232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11830 q = 1) (hb : d53233 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11830, d53233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11830, d53233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25038 (p : Pattern) (ha : d11886 p = 1) (hb : d53244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11831 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25037 q ha hb
    | true =>
      simp only [d11831, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11832 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11883 q = 1) (hb : d53241 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11883, d53241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11883, d53241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11884 q = 1) (hb : d53242 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11884, d53242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11884, d53242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11885 q = 1) (hb : d53243 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11885, d53243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11885, d53243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11886 q = 1) (hb : d53244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11886, d53244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11886, d53244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25039 (p : Pattern) (ha : d11892 p = 1) (hb : d53259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11887 q = 1) (hb : d53254 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11887, d53254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25038 q ha hb
    | true =>
      simp only [d11887, d53254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11888 q = 1) (hb : d53255 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11888, d53255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11888, d53255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11889 q = 1) (hb : d53256 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11889, d53256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11889, d53256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11890 q = 1) (hb : d53257 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11890, d53257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11890, d53257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11891 q = 1) (hb : d53258 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11891, d53258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11891, d53258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11892 q = 1) (hb : d53259 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11892, d53259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11892, d53259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25040 (p : Pattern) (ha : d84228 p = 1) (hb : d111138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11637 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11638 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11639 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53043 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11640 q = 1) (hb : d53044 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro211 q ha hb
    | true =>
      simp only [d11640, d53044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11641 q = 1) (hb : d53045 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11641, d53045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11642 q = 1) (hb : d53046 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11642, d53046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11643 q = 1) (hb : d53047 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11643, d53047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84227 q = 1) (hb : d111137 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84227, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84227, d111137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84228 q = 1) (hb : d111138 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84228, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84228, d111138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25041 (p : Pattern) (ha : d84234 p = 1) (hb : d111144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84233 q = 1) (hb : d111143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84233, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84233, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84234 q = 1) (hb : d111144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84234, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84234, d111144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25042 (p : Pattern) (ha : d84240 p = 1) (hb : d111150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25041 q ha hb
    | true =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84240 q = 1) (hb : d111150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84240, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84240, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25043 (p : Pattern) (ha : d84243 p = 1) (hb : d111153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84233 q = 1) (hb : d111143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84233, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84233, d111143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84243 q = 1) (hb : d111153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84243, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84243, d111153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25044 (p : Pattern) (ha : d84249 p = 1) (hb : d111159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25041 q ha hb
    | true =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84244 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25043 q ha hb
    | true =>
      simp only [d84244, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q hb ha
  have h7 (q : Pattern) (ha : d84245 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84245, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84245, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84246 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84246, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84246, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84247 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84247, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84247, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84248 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84248, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84248, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84249 q = 1) (hb : d111159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84249, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84249, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25045 (p : Pattern) (ha : d11683 p = 1) (hb : d53087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d53062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d53086 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d53086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d53086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11683 q = 1) (hb : d53087 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11683, d53087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11683, d53087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25046 (p : Pattern) (ha : d11693 p = 1) (hb : d53097 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d53095 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d53095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d53095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d53096 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d53096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d53096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11693 q = 1) (hb : d53097 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11693, d53097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11693, d53097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25047 (p : Pattern) (ha : d84254 p = 1) (hb : d111164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84253 q = 1) (hb : d111163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84253, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84253, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84254 q = 1) (hb : d111164 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84254, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84254, d111164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25048 (p : Pattern) (ha : d84261 p = 1) (hb : d111171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84259 q = 1) (hb : d111169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84259, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84259, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84260 q = 1) (hb : d111170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84260, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84260, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84261 q = 1) (hb : d111171 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84261, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84261, d111171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25049 (p : Pattern) (ha : d84266 p = 1) (hb : d111176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53028 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11697 q = 1) (hb : d53112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11697, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro231 q ha hb
    | true =>
      simp only [d11697, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11698 q = 1) (hb : d53113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11698, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11698, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11699 q = 1) (hb : d53114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11699, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11699, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53030 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11637 q = 1) (hb : d53031 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
    | true =>
      simp only [d11637, d53031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11638 q = 1) (hb : d53032 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11638, d53032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11639 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11639, d53033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11700 q = 1) (hb : d53115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11700, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84265 q = 1) (hb : d111175 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84265, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84265, d111175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84266 q = 1) (hb : d111176 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84266, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84266, d111176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25050 (p : Pattern) (ha : d84272 p = 1) (hb : d111182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84267 q = 1) (hb : d111177 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84267, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25049 q ha hb
    | true =>
      simp only [d84267, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84268 q = 1) (hb : d111178 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84268, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84268, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d111179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84269, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d111180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d111181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84272 q = 1) (hb : d111182 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84272, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84272, d111182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25051 (p : Pattern) (ha : d84278 p = 1) (hb : d111188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84275 q = 1) (hb : d111185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84275, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84275, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84276 q = 1) (hb : d111186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84276, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84276, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84277 q = 1) (hb : d111187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84277, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84277, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84278 q = 1) (hb : d111188 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84278, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84278, d111188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25052 (p : Pattern) (ha : d84284 p = 1) (hb : d111194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84255 q = 1) (hb : d111165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84255, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25047 q ha hb
    | true =>
      simp only [d84255, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25045 q hb ha
  have h2 (q : Pattern) (ha : d84256 q = 1) (hb : d111166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84256, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84256, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84257 q = 1) (hb : d111167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84257, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84257, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84258 q = 1) (hb : d111168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84258, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84258, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84262 q = 1) (hb : d111172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84262, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25048 q ha hb
    | true =>
      simp only [d84262, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25046 q hb ha
  have h6 (q : Pattern) (ha : d84263 q = 1) (hb : d111173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84263, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84263, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84264 q = 1) (hb : d111174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84264, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84264, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d111183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25050 q ha hb
    | true =>
      simp only [d84273, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25041 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d111184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84279 q = 1) (hb : d111189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84279, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25051 q ha hb
    | true =>
      simp only [d84279, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84280 q = 1) (hb : d111190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84280, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84280, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d111191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d111192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84282, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d111193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84283, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84284 q = 1) (hb : d111194 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84284, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84284, d111194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro25053 (p : Pattern) (ha : d11755 p = 1) (hb : d53133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11658 q = 1) (hb : d53062 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11658, d53062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11682 q = 1) (hb : d53086 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d53086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11682, d53086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11755 q = 1) (hb : d53133 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11755, d53133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11755, d53133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25054 (p : Pattern) (ha : d11761 p = 1) (hb : d53139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11657 q = 1) (hb : d53061 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11657, d53061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11691 q = 1) (hb : d53095 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d53095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11691, d53095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11692 q = 1) (hb : d53096 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d53096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11692, d53096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11761 q = 1) (hb : d53139 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11761, d53139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11761, d53139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25055 (p : Pattern) (ha : d84285 p = 1) (hb : d111195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d111142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d111142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84253 q = 1) (hb : d111163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84253, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84253, d111163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84285 q = 1) (hb : d111195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84285, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84285, d111195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25056 (p : Pattern) (ha : d84290 p = 1) (hb : d111200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11651 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25032 q ha hb
    | true =>
      simp only [d11651, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11652 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11652, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d111141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d111141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84259 q = 1) (hb : d111169 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84259, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84259, d111169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84260 q = 1) (hb : d111170 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84260, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84260, d111170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84290 q = 1) (hb : d111200 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84290, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84290, d111200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25057 (p : Pattern) (ha : d84294 p = 1) (hb : d111204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84267 q = 1) (hb : d111177 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84267, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25049 q ha hb
    | true =>
      simp only [d84267, d111177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84268 q = 1) (hb : d111178 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84268, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84268, d111178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d111179 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84269, d111179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d111180 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d111180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d111181 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d111181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84294 q = 1) (hb : d111204 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84294, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84294, d111204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25058 (p : Pattern) (ha : d84297 p = 1) (hb : d111207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d111139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25040 q ha hb
    | true =>
      simp only [d84229, d111139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d111140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d111140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84275 q = 1) (hb : d111185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84275, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84275, d111185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84276 q = 1) (hb : d111186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84276, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84276, d111186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84277 q = 1) (hb : d111187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84277, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84277, d111187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84297 q = 1) (hb : d111207 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84297, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84297, d111207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25059 (p : Pattern) (ha : d84303 p = 1) (hb : d111213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84255 q = 1) (hb : d111165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84255, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25047 q ha hb
    | true =>
      simp only [d84255, d111165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25045 q hb ha
  have h2 (q : Pattern) (ha : d84256 q = 1) (hb : d111166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84256, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84256, d111166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84257 q = 1) (hb : d111167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84257, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84257, d111167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84258 q = 1) (hb : d111168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84258, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84258, d111168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84262 q = 1) (hb : d111172 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84262, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25048 q ha hb
    | true =>
      simp only [d84262, d111172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25046 q hb ha
  have h6 (q : Pattern) (ha : d84263 q = 1) (hb : d111173 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84263, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84263, d111173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84264 q = 1) (hb : d111174 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84264, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84264, d111174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d111183 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25050 q ha hb
    | true =>
      simp only [d84273, d111183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25041 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d111184 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d111184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84279 q = 1) (hb : d111189 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84279, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25051 q ha hb
    | true =>
      simp only [d84279, d111189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84280 q = 1) (hb : d111190 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84280, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84280, d111190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d111191 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d111191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d111192 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84282, d111192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d111193 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84283, d111193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84286 q = 1) (hb : d111196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84286, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25055 q ha hb
    | true =>
      simp only [d84286, d111196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25053 q hb ha
  have h17 (q : Pattern) (ha : d84287 q = 1) (hb : d111197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84287, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84287, d111197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84288 q = 1) (hb : d111198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84288, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84288, d111198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84289 q = 1) (hb : d111199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84289, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84289, d111199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84291 q = 1) (hb : d111201 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84291, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25056 q ha hb
    | true =>
      simp only [d84291, d111201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25054 q hb ha
  have h21 (q : Pattern) (ha : d84292 q = 1) (hb : d111202 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84292, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84292, d111202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84293 q = 1) (hb : d111203 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84293, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84293, d111203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84295 q = 1) (hb : d111205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25057 q ha hb
    | true =>
      simp only [d84295, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25043 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84296 q = 1) (hb : d111206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84296, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84298 q = 1) (hb : d111208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84298, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25058 q ha hb
    | true =>
      simp only [d84298, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84299 q = 1) (hb : d111209 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84299, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84299, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84300 q = 1) (hb : d111210 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84300, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84301 q = 1) (hb : d111211 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84301, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84301, d111211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84302 q = 1) (hb : d111212 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84302, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84302, d111212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84303 q = 1) (hb : d111213 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84303, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84303, d111213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro25060 (p : Pattern) (ha : d84305 p = 1) (hb : d111215 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25041 q ha hb
    | true =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11779 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q ha hb
    | true =>
      simp only [d11779, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11780 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11780, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11781 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11781, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11782 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11782, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11783 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11783, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84305 q = 1) (hb : d111215 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84305, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84305, d111215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro25061 (p : Pattern) (ha : d84312 p = 1) (hb : d111222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84295 q = 1) (hb : d111205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25057 q ha hb
    | true =>
      simp only [d84295, d111205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25043 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84296 q = 1) (hb : d111206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84296, d111206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84298 q = 1) (hb : d111208 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84298, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25058 q ha hb
    | true =>
      simp only [d84298, d111208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84299 q = 1) (hb : d111209 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84299, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84299, d111209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84300 q = 1) (hb : d111210 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84300, d111210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84310 q = 1) (hb : d111220 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84310, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84310, d111220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84311 q = 1) (hb : d111221 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84311, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84311, d111221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84312 q = 1) (hb : d111222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d111222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25062 (p : Pattern) (ha : d84319 p = 1) (hb : d111229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53199 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11805 q = 1) (hb : d53200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11805, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro235 q ha hb
    | true =>
      simp only [d11805, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11806 q = 1) (hb : d53201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11806, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11806, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11807 q = 1) (hb : d53202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11807, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11807, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11808 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11809 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11810 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11811 q = 1) (hb : d53208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11811, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11811, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84318 q = 1) (hb : d111228 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84318, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84318, d111228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84319 q = 1) (hb : d111229 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84319, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84319, d111229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25063 (p : Pattern) (ha : d84323 p = 1) (hb : d111233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53204 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11808 q = 1) (hb : d53205 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
    | true =>
      simp only [d11808, d53205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11809 q = 1) (hb : d53206 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11809, d53206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11810 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11810, d53207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53214 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11812 q = 1) (hb : d53215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro225 q ha hb
    | true =>
      simp only [d11812, d53215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11813 q = 1) (hb : d53216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11813, d53216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11814 q = 1) (hb : d53217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11814, d53217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11815 q = 1) (hb : d53218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11815, d53218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84322 q = 1) (hb : d111232 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84322, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84322, d111232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84323 q = 1) (hb : d111233 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84323, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84323, d111233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25064 (p : Pattern) (ha : d84329 p = 1) (hb : d111239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84320 q = 1) (hb : d111230 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84320, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25062 q ha hb
    | true =>
      simp only [d84320, d111230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84321 q = 1) (hb : d111231 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84321, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84321, d111231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84324 q = 1) (hb : d111234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25063 q ha hb
    | true =>
      simp only [d84324, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84325 q = 1) (hb : d111235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84326 q = 1) (hb : d111236 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84326, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84326, d111236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84327 q = 1) (hb : d111237 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84327, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84327, d111237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84328 q = 1) (hb : d111238 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84328, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84328, d111238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84329 q = 1) (hb : d111239 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84329, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84329, d111239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25065 (p : Pattern) (ha : d84333 p = 1) (hb : d111243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84324 q = 1) (hb : d111234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25063 q ha hb
    | true =>
      simp only [d84324, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84325 q = 1) (hb : d111235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11831 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25037 q ha hb
    | true =>
      simp only [d11831, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11832 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11832, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84330 q = 1) (hb : d111240 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84330, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84330, d111240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84331 q = 1) (hb : d111241 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84331, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84331, d111241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84332 q = 1) (hb : d111242 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84332, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84332, d111242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84333 q = 1) (hb : d111243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84333, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84333, d111243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25066 (p : Pattern) (ha : d84340 p = 1) (hb : d111249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84324 q = 1) (hb : d111234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25063 q ha hb
    | true =>
      simp only [d84324, d111234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84325 q = 1) (hb : d111235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d111235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84337 q = 1) (hb : d111246 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84337, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84337, d111246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84338 q = 1) (hb : d111247 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84338, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84338, d111247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84339 q = 1) (hb : d111248 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84339, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84339, d111248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84340 q = 1) (hb : d111249 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84340, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84340, d111249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25067 (p : Pattern) (ha : d84346 p = 1) (hb : d111255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84334 q = 1) (hb : d111244 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84334, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25064 q ha hb
    | true =>
      simp only [d84334, d111244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25065 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84335 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d111245 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84336, d111245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84341 q = 1) (hb : d111250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84341, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25066 q ha hb
    | true =>
      simp only [d84341, d111250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84342 q = 1) (hb : d111251 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84342, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84342, d111251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84343 q = 1) (hb : d111252 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d111252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84344 q = 1) (hb : d111253 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d111253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84345 q = 1) (hb : d111254 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d111254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84346 q = 1) (hb : d111255 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d111255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25068 (p : Pattern) (ha : d84352 p = 1) (hb : d111261 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84241 q = 1) (hb : d111151 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84241, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84241, d111151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25042 q ha hb
  have h2 (q : Pattern) (ha : d84242 q = 1) (hb : d111152 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84242, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84242, d111152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84250 q = 1) (hb : d111160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84250, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25042 q ha hb
    | true =>
      simp only [d84250, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25044 q ha hb
  have h4 (q : Pattern) (ha : d84251 q = 1) (hb : d111161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84251, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84251, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84252 q = 1) (hb : d111162 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84252, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84252, d111162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84304 q = 1) (hb : d111214 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84304, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25052 q ha hb
    | true =>
      simp only [d84304, d111214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25059 q ha hb
  have h7 (q : Pattern) (ha : d84306 q = 1) (hb : d111216 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84306, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25060 q ha hb
    | true =>
      simp only [d84306, d111216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25035 q hb ha
  have h8 (q : Pattern) (ha : d84307 q = 1) (hb : d111217 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84307, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84307, d111217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84308 q = 1) (hb : d111218 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84308, d111218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84309 q = 1) (hb : d111219 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84309, d111219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84313 q = 1) (hb : d111223 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84313, d111223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25061 q ha hb
  have h12 (q : Pattern) (ha : d11800 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11800, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11800, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25036 q ha hb
  have h13 (q : Pattern) (ha : d84314 q = 1) (hb : d111224 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84314, d111224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84315 q = 1) (hb : d111225 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84315, d111225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84316 q = 1) (hb : d111226 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84316, d111226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84317 q = 1) (hb : d111227 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84317, d111227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84347 q = 1) (hb : d111256 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84347, d111256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25067 q ha hb
  have h18 (q : Pattern) (ha : d11893 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11893, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11893, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25039 q ha hb
  have h19 (q : Pattern) (ha : d84348 q = 1) (hb : d111257 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84348, d111257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84349 q = 1) (hb : d111258 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84349, d111258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84350 q = 1) (hb : d111259 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84350, d111259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84351 q = 1) (hb : d111260 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84351, d111260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84352 q = 1) (hb : d111261 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84352, d111261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25069 (p : Pattern) (ha : d84358 p = 1) (hb : d111267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d111262 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d111262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25068 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d111263 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d111263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d111264 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d111264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d111265 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d111265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d111266 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d111266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d111267 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d111267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25070 (p : Pattern) (ha : d11922 p = 1) (hb : d53375 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11912 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11913 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11914 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11916 q = 1) (hb : d53369 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11916, d53369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11921 q = 1) (hb : d53374 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11921, d53374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11921, d53374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11922 q = 1) (hb : d53375 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11922, d53375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11922, d53375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25071 (p : Pattern) (ha : d11932 p = 1) (hb : d53385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d53383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11931 q = 1) (hb : d53384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d53384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11931, d53384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11932 q = 1) (hb : d53385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11932, d53385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11932, d53385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25072 (p : Pattern) (ha : d11942 p = 1) (hb : d53395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d53383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11931 q = 1) (hb : d53384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d53384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11931, d53384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11942 q = 1) (hb : d53395 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11942, d53395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11942, d53395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25073 (p : Pattern) (ha : d12062 p = 1) (hb : d53481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12051 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
    | true =>
      simp only [d12051, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12052 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12053 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12053, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12054 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12055 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12057 q = 1) (hb : d53476 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d53476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q ha hb
    | true =>
      simp only [d12057, d53476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12058 q = 1) (hb : d53477 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d53477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, d53477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12059 q = 1) (hb : d53478 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d53478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12059, d53478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12060 q = 1) (hb : d53479 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d53479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, d53479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12061 q = 1) (hb : d53480 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d53480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, d53480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d12062 q = 1) (hb : d53481 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12062, d53481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12062, d53481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25074 (p : Pattern) (ha : d12071 p = 1) (hb : d53490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12057 q = 1) (hb : d53476 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d53476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q ha hb
    | true =>
      simp only [d12057, d53476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12058 q = 1) (hb : d53477 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d53477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12058, d53477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12059 q = 1) (hb : d53478 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d53478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12059, d53478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12060 q = 1) (hb : d53479 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d53479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12060, d53479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12061 q = 1) (hb : d53480 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d53480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12061, d53480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12071 q = 1) (hb : d53490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12071, d53490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12071, d53490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25075 (p : Pattern) (ha : d12102 p = 1) (hb : d53550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12084 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12085 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12086 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12092 q = 1) (hb : d53540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12092, d53540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12101 q = 1) (hb : d53549 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12101, d53549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12101, d53549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12102 q = 1) (hb : d53550 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12102, d53550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12102, d53550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro25076 (p : Pattern) (ha : d12158 p = 1) (hb : d53561 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12103 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25075 q ha hb
    | true =>
      simp only [d12103, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12104 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12155 q = 1) (hb : d53558 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12155, d53558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12155, d53558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12156 q = 1) (hb : d53559 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12156, d53559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12156, d53559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12157 q = 1) (hb : d53560 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12157, d53560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12157, d53560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12158 q = 1) (hb : d53561 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12158, d53561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12158, d53561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25077 (p : Pattern) (ha : d12164 p = 1) (hb : d53576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12159 q = 1) (hb : d53571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12159, d53571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25076 q ha hb
    | true =>
      simp only [d12159, d53571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d12160 q = 1) (hb : d53572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12160, d53572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12160, d53572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12161 q = 1) (hb : d53573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12161, d53573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12161, d53573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12162 q = 1) (hb : d53574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12162, d53574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12162, d53574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12163 q = 1) (hb : d53575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12163, d53575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12163, d53575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12164 q = 1) (hb : d53576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12164, d53576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12164, d53576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25078 (p : Pattern) (ha : d84364 p = 1) (hb : d111273 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11909 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11910 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11911 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53364 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11912 q = 1) (hb : d53365 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro270 q ha hb
    | true =>
      simp only [d11912, d53365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11913 q = 1) (hb : d53366 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11913, d53366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11914 q = 1) (hb : d53367 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11914, d53367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11915 q = 1) (hb : d53368 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11915, d53368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84363 q = 1) (hb : d111272 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84363, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84363, d111272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84364 q = 1) (hb : d111273 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84364, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84364, d111273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25079 (p : Pattern) (ha : d84370 p = 1) (hb : d111279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84369 q = 1) (hb : d111278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84369, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84369, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84370 q = 1) (hb : d111279 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84370, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84370, d111279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25080 (p : Pattern) (ha : d84376 p = 1) (hb : d111285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25079 q ha hb
    | true =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84376 q = 1) (hb : d111285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84376, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84376, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25081 (p : Pattern) (ha : d84379 p = 1) (hb : d111288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84369 q = 1) (hb : d111278 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84369, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84369, d111278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84379 q = 1) (hb : d111288 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84379, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84379, d111288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25082 (p : Pattern) (ha : d84385 p = 1) (hb : d111294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25079 q ha hb
    | true =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84380 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25081 q ha hb
    | true =>
      simp only [d84380, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q hb ha
  have h7 (q : Pattern) (ha : d84381 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84381, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84381, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84382 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84382, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84382, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84383 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84383, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84383, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84384 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84384, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84384, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84385 q = 1) (hb : d111294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84385, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84385, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25083 (p : Pattern) (ha : d11955 p = 1) (hb : d53408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d53383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11954 q = 1) (hb : d53407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d53407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, d53407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11955 q = 1) (hb : d53408 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11955, d53408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11955, d53408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25084 (p : Pattern) (ha : d11965 p = 1) (hb : d53418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11963 q = 1) (hb : d53416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d53416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, d53416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11964 q = 1) (hb : d53417 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d53417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11964, d53417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11965 q = 1) (hb : d53418 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11965, d53418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11965, d53418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25085 (p : Pattern) (ha : d84390 p = 1) (hb : d111299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84389 q = 1) (hb : d111298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84389, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84389, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84390 q = 1) (hb : d111299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84390, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84390, d111299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25086 (p : Pattern) (ha : d84397 p = 1) (hb : d111306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84395 q = 1) (hb : d111304 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84395, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84395, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84396 q = 1) (hb : d111305 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84396, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84396, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84397 q = 1) (hb : d111306 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84397, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84397, d111306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25087 (p : Pattern) (ha : d84402 p = 1) (hb : d111311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53349 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11969 q = 1) (hb : d53429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11969, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro290 q ha hb
    | true =>
      simp only [d11969, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11970 q = 1) (hb : d53430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11970, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11970, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11971 q = 1) (hb : d53431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11971, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11971, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53351 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11909 q = 1) (hb : d53352 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
    | true =>
      simp only [d11909, d53352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11910 q = 1) (hb : d53353 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11910, d53353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11911 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11911, d53354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11972 q = 1) (hb : d53432 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11972, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11972, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84401 q = 1) (hb : d111310 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84401, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84401, d111310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84402 q = 1) (hb : d111311 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84402, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84402, d111311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25088 (p : Pattern) (ha : d84408 p = 1) (hb : d111317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84403 q = 1) (hb : d111312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84403, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25087 q ha hb
    | true =>
      simp only [d84403, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84404 q = 1) (hb : d111313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84404, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84404, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d111314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84405, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d111315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d111316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84408 q = 1) (hb : d111317 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84408, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84408, d111317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25089 (p : Pattern) (ha : d84414 p = 1) (hb : d111323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84411 q = 1) (hb : d111320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84411, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84411, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84412 q = 1) (hb : d111321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84412, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84412, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84413 q = 1) (hb : d111322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84413, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84413, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84414 q = 1) (hb : d111323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84414, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84414, d111323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25090 (p : Pattern) (ha : d84420 p = 1) (hb : d111329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84391 q = 1) (hb : d111300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84391, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25085 q ha hb
    | true =>
      simp only [d84391, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25083 q hb ha
  have h2 (q : Pattern) (ha : d84392 q = 1) (hb : d111301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84392, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84392, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84393 q = 1) (hb : d111302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84393, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84393, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84394 q = 1) (hb : d111303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84394, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84394, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84398 q = 1) (hb : d111307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84398, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25086 q ha hb
    | true =>
      simp only [d84398, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25084 q hb ha
  have h6 (q : Pattern) (ha : d84399 q = 1) (hb : d111308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84399, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84399, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84400 q = 1) (hb : d111309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84400, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84400, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d111318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25088 q ha hb
    | true =>
      simp only [d84409, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25079 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d111319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84415 q = 1) (hb : d111324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84415, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25089 q ha hb
    | true =>
      simp only [d84415, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84416 q = 1) (hb : d111325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84416, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84416, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d111326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d111327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84418, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d111328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84419, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84420 q = 1) (hb : d111329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84420, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84420, d111329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro25091 (p : Pattern) (ha : d12027 p = 1) (hb : d53450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11930 q = 1) (hb : d53383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11930, d53383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11954 q = 1) (hb : d53407 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d53407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11954, d53407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12027 q = 1) (hb : d53450 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12027, d53450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12027, d53450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25092 (p : Pattern) (ha : d12033 p = 1) (hb : d53456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11929 q = 1) (hb : d53382 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11929, d53382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11963 q = 1) (hb : d53416 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d53416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11963, d53416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11964 q = 1) (hb : d53417 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d53417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11964, d53417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d12033 q = 1) (hb : d53456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12033, d53456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12033, d53456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25093 (p : Pattern) (ha : d84421 p = 1) (hb : d111330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d111277 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d111277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84389 q = 1) (hb : d111298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84389, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84389, d111298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84421 q = 1) (hb : d111330 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84421, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84421, d111330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25094 (p : Pattern) (ha : d84426 p = 1) (hb : d111335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11923 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25070 q ha hb
    | true =>
      simp only [d11923, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11924 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11924, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d111276 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d111276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84395 q = 1) (hb : d111304 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84395, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84395, d111304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84396 q = 1) (hb : d111305 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84396, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84396, d111305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84426 q = 1) (hb : d111335 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84426, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84426, d111335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25095 (p : Pattern) (ha : d84430 p = 1) (hb : d111339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84403 q = 1) (hb : d111312 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84403, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25087 q ha hb
    | true =>
      simp only [d84403, d111312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84404 q = 1) (hb : d111313 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84404, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84404, d111313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d111314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84405, d111314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d111315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d111315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d111316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d111316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84430 q = 1) (hb : d111339 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84430, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84430, d111339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25096 (p : Pattern) (ha : d84433 p = 1) (hb : d111342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d111274 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25078 q ha hb
    | true =>
      simp only [d84365, d111274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d111275 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d111275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84411 q = 1) (hb : d111320 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84411, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84411, d111320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84412 q = 1) (hb : d111321 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84412, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84412, d111321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84413 q = 1) (hb : d111322 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84413, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84413, d111322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84433 q = 1) (hb : d111342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84433, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84433, d111342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25097 (p : Pattern) (ha : d84439 p = 1) (hb : d111348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84391 q = 1) (hb : d111300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84391, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25085 q ha hb
    | true =>
      simp only [d84391, d111300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25083 q hb ha
  have h2 (q : Pattern) (ha : d84392 q = 1) (hb : d111301 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84392, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84392, d111301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84393 q = 1) (hb : d111302 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84393, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84393, d111302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84394 q = 1) (hb : d111303 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84394, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84394, d111303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84398 q = 1) (hb : d111307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84398, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25086 q ha hb
    | true =>
      simp only [d84398, d111307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25084 q hb ha
  have h6 (q : Pattern) (ha : d84399 q = 1) (hb : d111308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84399, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84399, d111308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84400 q = 1) (hb : d111309 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84400, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84400, d111309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d111318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25088 q ha hb
    | true =>
      simp only [d84409, d111318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25079 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d111319 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d111319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84415 q = 1) (hb : d111324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84415, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25089 q ha hb
    | true =>
      simp only [d84415, d111324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84416 q = 1) (hb : d111325 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84416, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84416, d111325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d111326 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d111326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d111327 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84418, d111327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d111328 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84419, d111328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84422 q = 1) (hb : d111331 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84422, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25093 q ha hb
    | true =>
      simp only [d84422, d111331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25091 q hb ha
  have h17 (q : Pattern) (ha : d84423 q = 1) (hb : d111332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84423, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84423, d111332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84424 q = 1) (hb : d111333 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84424, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84424, d111333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84425 q = 1) (hb : d111334 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84425, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84425, d111334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84427 q = 1) (hb : d111336 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84427, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25094 q ha hb
    | true =>
      simp only [d84427, d111336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25092 q hb ha
  have h21 (q : Pattern) (ha : d84428 q = 1) (hb : d111337 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84428, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84428, d111337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84429 q = 1) (hb : d111338 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84429, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84429, d111338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84431 q = 1) (hb : d111340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25095 q ha hb
    | true =>
      simp only [d84431, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25081 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84432 q = 1) (hb : d111341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84432, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84434 q = 1) (hb : d111343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84434, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25096 q ha hb
    | true =>
      simp only [d84434, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84435 q = 1) (hb : d111344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84435, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84435, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84436 q = 1) (hb : d111345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84436, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84437 q = 1) (hb : d111346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84437, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84437, d111346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84438 q = 1) (hb : d111347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84438, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84438, d111347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84439 q = 1) (hb : d111348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84439, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84439, d111348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro25098 (p : Pattern) (ha : d84441 p = 1) (hb : d111350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25079 q ha hb
    | true =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12051 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q ha hb
    | true =>
      simp only [d12051, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d12052 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12052, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12053 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d12053, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12054 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12054, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d12055 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12055, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84441 q = 1) (hb : d111350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84441, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84441, d111350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro25099 (p : Pattern) (ha : d84448 p = 1) (hb : d111357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84431 q = 1) (hb : d111340 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25095 q ha hb
    | true =>
      simp only [d84431, d111340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25081 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84432 q = 1) (hb : d111341 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84432, d111341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84434 q = 1) (hb : d111343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84434, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25096 q ha hb
    | true =>
      simp only [d84434, d111343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84435 q = 1) (hb : d111344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84435, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84435, d111344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84436 q = 1) (hb : d111345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84436, d111345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84446 q = 1) (hb : d111355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84446, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84446, d111355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84447 q = 1) (hb : d111356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84447, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84447, d111356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84448 q = 1) (hb : d111357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d111357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25100 (p : Pattern) (ha : d84455 p = 1) (hb : d111364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53516 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12077 q = 1) (hb : d53517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12077, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro294 q ha hb
    | true =>
      simp only [d12077, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12078 q = 1) (hb : d53518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12078, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12078, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12079 q = 1) (hb : d53519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12079, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12079, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12080 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12081 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12082 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12083 q = 1) (hb : d53525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12083, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12083, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84454 q = 1) (hb : d111363 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84454, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84454, d111363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84455 q = 1) (hb : d111364 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84455, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84455, d111364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25101 (p : Pattern) (ha : d84459 p = 1) (hb : d111368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53521 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12080 q = 1) (hb : d53522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
    | true =>
      simp only [d12080, d53522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12081 q = 1) (hb : d53523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12081, d53523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12082 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12082, d53524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53531 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12084 q = 1) (hb : d53532 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro284 q ha hb
    | true =>
      simp only [d12084, d53532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d12085 q = 1) (hb : d53533 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12085, d53533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d12086 q = 1) (hb : d53534 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12086, d53534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d12087 q = 1) (hb : d53535 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12087, d53535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84458 q = 1) (hb : d111367 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84458, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84458, d111367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d84459 q = 1) (hb : d111368 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84459, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84459, d111368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro25102 (p : Pattern) (ha : d84465 p = 1) (hb : d111374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84456 q = 1) (hb : d111365 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84456, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25100 q ha hb
    | true =>
      simp only [d84456, d111365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84457 q = 1) (hb : d111366 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84457, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84457, d111366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84460 q = 1) (hb : d111369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25101 q ha hb
    | true =>
      simp only [d84460, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84461 q = 1) (hb : d111370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84462 q = 1) (hb : d111371 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84462, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84462, d111371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84463 q = 1) (hb : d111372 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84463, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84463, d111372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84464 q = 1) (hb : d111373 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84464, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84464, d111373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84465 q = 1) (hb : d111374 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84465, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84465, d111374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25103 (p : Pattern) (ha : d84469 p = 1) (hb : d111378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84460 q = 1) (hb : d111369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25101 q ha hb
    | true =>
      simp only [d84460, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84461 q = 1) (hb : d111370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12103 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25075 q ha hb
    | true =>
      simp only [d12103, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12104 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12104, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84466 q = 1) (hb : d111375 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84466, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84466, d111375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84467 q = 1) (hb : d111376 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84467, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84467, d111376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84468 q = 1) (hb : d111377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84468, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84468, d111377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84469 q = 1) (hb : d111378 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84469, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84469, d111378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro25104 (p : Pattern) (ha : d84476 p = 1) (hb : d111384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84460 q = 1) (hb : d111369 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25101 q ha hb
    | true =>
      simp only [d84460, d111369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84461 q = 1) (hb : d111370 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d111370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84473 q = 1) (hb : d111381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84473, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84473, d111381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84474 q = 1) (hb : d111382 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84474, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84474, d111382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84475 q = 1) (hb : d111383 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84475, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84475, d111383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84476 q = 1) (hb : d111384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84476, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84476, d111384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25105 (p : Pattern) (ha : d84482 p = 1) (hb : d111390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84470 q = 1) (hb : d111379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84470, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25102 q ha hb
    | true =>
      simp only [d84470, d111379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25103 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d111380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84472, d111380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84477 q = 1) (hb : d111385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84477, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25104 q ha hb
    | true =>
      simp only [d84477, d111385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84478 q = 1) (hb : d111386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84478, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84478, d111386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84479 q = 1) (hb : d111387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d111387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84480 q = 1) (hb : d111388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d111388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84481 q = 1) (hb : d111389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d111389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84482 q = 1) (hb : d111390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d111390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro25106 (p : Pattern) (ha : d84488 p = 1) (hb : d111396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84377 q = 1) (hb : d111286 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84377, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84377, d111286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25080 q ha hb
  have h2 (q : Pattern) (ha : d84378 q = 1) (hb : d111287 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84378, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84378, d111287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84386 q = 1) (hb : d111295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84386, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25080 q ha hb
    | true =>
      simp only [d84386, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25082 q ha hb
  have h4 (q : Pattern) (ha : d84387 q = 1) (hb : d111296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84387, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84387, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84388 q = 1) (hb : d111297 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84388, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84388, d111297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84440 q = 1) (hb : d111349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84440, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25090 q ha hb
    | true =>
      simp only [d84440, d111349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25097 q ha hb
  have h7 (q : Pattern) (ha : d84442 q = 1) (hb : d111351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84442, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25098 q ha hb
    | true =>
      simp only [d84442, d111351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25073 q hb ha
  have h8 (q : Pattern) (ha : d84443 q = 1) (hb : d111352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84443, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84443, d111352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84444 q = 1) (hb : d111353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84444, d111353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84445 q = 1) (hb : d111354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84445, d111354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84449 q = 1) (hb : d111358 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84449, d111358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25099 q ha hb
  have h12 (q : Pattern) (ha : d12072 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12072, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12072, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25074 q ha hb
  have h13 (q : Pattern) (ha : d84450 q = 1) (hb : d111359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84450, d111359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84451 q = 1) (hb : d111360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84451, d111360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84452 q = 1) (hb : d111361 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84452, d111361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84453 q = 1) (hb : d111362 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84453, d111362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84483 q = 1) (hb : d111391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84483, d111391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25105 q ha hb
  have h18 (q : Pattern) (ha : d12165 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12165, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12165, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25077 q ha hb
  have h19 (q : Pattern) (ha : d84484 q = 1) (hb : d111392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84484, d111392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84485 q = 1) (hb : d111393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84485, d111393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84486 q = 1) (hb : d111394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84486, d111394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84487 q = 1) (hb : d111395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84487, d111395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84488 q = 1) (hb : d111396 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84488, d111396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro25107 (p : Pattern) (ha : d84494 p = 1) (hb : d111402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d111397 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d111397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25106 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d111398 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d111398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d111399 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d111399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d111400 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d111400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d111401 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d111401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d111402 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d111402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25108 (p : Pattern) (ha : d84500 p = 1) (hb : d111408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d110869 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24919 q ha hb
    | true =>
      simp only [d83957, d110869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24955 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d111001 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d111001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24993 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d111002 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d111002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d111134 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d111134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25031 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d111135 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d111135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d111136 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d111136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d111268 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d111268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25069 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d111269 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d111269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d111270 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d111270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d111271 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d111271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d111403 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d111403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25107 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d111404 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d111404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d111405 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d111405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d111406 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d111406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d111407 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d111407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d111408 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d111408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro25109 (p : Pattern) (ha : d84506 p = 1) (hb : d111414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d111409 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25108 q ha hb
    | true =>
      simp only [d84501, d111409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d111410 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d111410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d111411 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d111411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d111412 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d111412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d111413 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d111413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d111414 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d111414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25110 (p : Pattern) (ha : d84512 p = 1) (hb : d111420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d111415 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25109 q ha hb
    | true =>
      simp only [d84507, d111415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d111416 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d111416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d111417 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d111417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d111418 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d111418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d111419 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d111419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d111420 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d111420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25111 (p : Pattern) (ha : d84518 p = 1) (hb : d111426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d111421 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25110 q ha hb
    | true =>
      simp only [d84513, d111421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d111422 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d111422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d111423 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d111423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d111424 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d111424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d111425 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d111425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d111426 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d111426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25112 (p : Pattern) (ha : d84524 p = 1) (hb : d111432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d111427 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25111 q ha hb
    | true =>
      simp only [d84519, d111427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d111428 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d111428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d111429 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d111429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d111430 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d111430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d111431 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d111431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d111432 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d111432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25113 (p : Pattern) (ha : d84530 p = 1) (hb : d111438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d111433 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25112 q ha hb
    | true =>
      simp only [d84525, d111433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d111434 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d111434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d111435 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d111435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d111436 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d111436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d111437 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d111437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d111438 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d111438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25114 (p : Pattern) (ha : d84536 p = 1) (hb : d111444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d111439 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25113 q ha hb
    | true =>
      simp only [d84531, d111439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d111440 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d111440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d111441 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d111441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d111442 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d111442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d111443 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d111443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d111444 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d111444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25115 (p : Pattern) (ha : d84542 p = 1) (hb : d111450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d111445 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25114 q ha hb
    | true =>
      simp only [d84537, d111445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d111446 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d111446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d111447 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d111447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d111448 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d111448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d111449 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d111449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d111450 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d111450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25116 (p : Pattern) (ha : d107483 p = 1) (hb : d109112 p = 1) : d111453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d107483 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d107483 q = 1) : d110591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24715 q ha hb
    | true =>
      simp only [d10668, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10722 q = 1) (hb : d107483 q = 1) : d110641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10723 q = 1) (hb : d107483 q = 1) : d110642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10723, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10724 q = 1) (hb : d107483 q = 1) : d110643 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10725 q = 1) (hb : d107483 q = 1) : d110644 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109112 q = 1) : d111453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109112, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109112, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro25117 (p : Pattern) (ha : d107483 p = 1) (hb : d109122 p = 1) : d111463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d107483 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d107483 q = 1) : d110617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24719 q ha hb
    | true =>
      simp only [d10698, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109118 q = 1) : d111459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109118, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109118, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109119 q = 1) : d111460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109119, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109119, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109120 q = 1) : d111461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109120, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109120, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109121 q = 1) : d111462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109121, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109121, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109122 q = 1) : d111463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109122, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109122, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25118 (p : Pattern) (ha : d107483 p = 1) (hb : d109128 p = 1) : d111469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10727 q = 1) (hb : d107483 q = 1) : d110646 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24722 q ha hb
    | true =>
      simp only [d10727, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24723 q ha hb
  have h2 (q : Pattern) (ha : d10728 q = 1) (hb : d107483 q = 1) : d110647 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10728, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109110 q = 1) : d111451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109110, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109110, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109111 q = 1) : d111452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109111, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109111, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109113 q = 1) : d111454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109113, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109113, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25116 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109114 q = 1) : d111455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109114, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109114, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109115 q = 1) : d111456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109115, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109115, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109116 q = 1) : d111457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109116, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109116, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109117 q = 1) : d111458 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109117, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109117, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109123 q = 1) : d111464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109123, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109123, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25117 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109124 q = 1) : d111465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109124, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109124, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109125 q = 1) : d111466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109125, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109125, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109126 q = 1) : d111467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109126, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109126, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109127 q = 1) : d111468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109127, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109127, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109128 q = 1) : d111469 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109128, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109128, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25119 (p : Pattern) (ha : d107483 p = 1) (hb : d109134 p = 1) : d111475 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d107483 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109129 q = 1) : d111470 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109129, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109129, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25118 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109130 q = 1) : d111471 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109130, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109130, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109131 q = 1) : d111472 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109131, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109131, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109132 q = 1) : d111473 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109132, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109132, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109133 q = 1) : d111474 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109133, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109133, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109134 q = 1) : d111475 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109134, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109134, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25120 (p : Pattern) (ha : d107483 p = 1) (hb : d109137 p = 1) : d111478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10889 q = 1) (hb : d107483 q = 1) : d10889 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10890 q = 1) (hb : d107483 q = 1) : d110759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24746 q ha hb
    | true =>
      simp only [d10890, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10891 q = 1) (hb : d107483 q = 1) : d110760 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10892 q = 1) (hb : d107483 q = 1) : d110761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10892, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10893 q = 1) (hb : d107483 q = 1) : d110762 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10894 q = 1) (hb : d107483 q = 1) : d110763 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109137 q = 1) : d111478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109137, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109137, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro25121 (p : Pattern) (ha : d107483 p = 1) (hb : d109148 p = 1) : d111489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11076 q = 1) (hb : d107483 q = 1) : d11076 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109143 q = 1) : d111484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109143, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24764 q hb ha
    | true =>
      simp only [d109143, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109144 q = 1) : d111485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109144, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109144, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109145 q = 1) : d111486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109145, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109145, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109146 q = 1) : d111487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109146, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109146, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109147 q = 1) : d111488 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109147, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109147, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109148 q = 1) : d111489 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109148, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109148, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25122 (p : Pattern) (ha : d107483 p = 1) (hb : d109154 p = 1) : d111495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10896 q = 1) (hb : d107483 q = 1) : d110765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24745 q ha hb
    | true =>
      simp only [d10896, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24747 q ha hb
  have h2 (q : Pattern) (ha : d10897 q = 1) (hb : d107483 q = 1) : d110766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10897, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109135 q = 1) : d111476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109135, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109135, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109136 q = 1) : d111477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109136, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109136, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109138 q = 1) : d111479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109138, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109138, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25120 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109139 q = 1) : d111480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109139, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109139, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109140 q = 1) : d111481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109140, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109140, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109141 q = 1) : d111482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109141, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109141, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109142 q = 1) : d111483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109142, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109142, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109149 q = 1) : d111490 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109149, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109149, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25121 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109150 q = 1) : d111491 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109150, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109150, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109151 q = 1) : d111492 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109151, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109151, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109152 q = 1) : d111493 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109152, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109152, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109153 q = 1) : d111494 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109153, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109153, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109154 q = 1) : d111495 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109154, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109154, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25123 (p : Pattern) (ha : d107483 p = 1) (hb : d109160 p = 1) : d111501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109155 q = 1) : d111496 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109155, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109155, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25122 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109156 q = 1) : d111497 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109156, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109156, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109157 q = 1) : d111498 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109157, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109157, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109158 q = 1) : d111499 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109158, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109158, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109159 q = 1) : d111500 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109159, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109159, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109160 q = 1) : d111501 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109160, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109160, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25124 (p : Pattern) (ha : d107483 p = 1) (hb : d109164 p = 1) : d111505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11129 q = 1) (hb : d107483 q = 1) : d11129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11130 q = 1) (hb : d107483 q = 1) : d110887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24772 q ha hb
    | true =>
      simp only [d11130, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11131 q = 1) (hb : d107483 q = 1) : d110888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11132 q = 1) (hb : d107483 q = 1) : d110889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11132, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11133 q = 1) (hb : d107483 q = 1) : d110890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11134 q = 1) (hb : d107483 q = 1) : d110891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109164 q = 1) : d111505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109164, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109164, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro25125 (p : Pattern) (ha : d107483 p = 1) (hb : d109175 p = 1) : d111516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11345 q = 1) (hb : d107483 q = 1) : d11345 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109170 q = 1) : d111511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109170, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24791 q hb ha
    | true =>
      simp only [d109170, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109171 q = 1) : d111512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109171, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109171, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109172 q = 1) : d111513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109172, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109172, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109173 q = 1) : d111514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109173, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109173, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109174 q = 1) : d111515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109174, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109174, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109175 q = 1) : d111516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109175, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109175, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25126 (p : Pattern) (ha : d107483 p = 1) (hb : d109181 p = 1) : d111522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11136 q = 1) (hb : d107483 q = 1) : d110893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24771 q ha hb
    | true =>
      simp only [d11136, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24773 q ha hb
  have h2 (q : Pattern) (ha : d11137 q = 1) (hb : d107483 q = 1) : d110894 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11137, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109162 q = 1) : d111503 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109162, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109162, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109163 q = 1) : d111504 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109163, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109163, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109165 q = 1) : d111506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109165, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109165, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25124 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109166 q = 1) : d111507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109166, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109166, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109167 q = 1) : d111508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109167, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109167, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109168 q = 1) : d111509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109168, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109168, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109169 q = 1) : d111510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109169, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109169, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109176 q = 1) : d111517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109176, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109176, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25125 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109177 q = 1) : d111518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109177, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109177, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109178 q = 1) : d111519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109178, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109178, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109179 q = 1) : d111520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109179, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109179, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109180 q = 1) : d111521 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109180, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109180, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109181 q = 1) : d111522 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109181, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109181, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25127 (p : Pattern) (ha : d107483 p = 1) (hb : d109187 p = 1) : d111528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109182 q = 1) : d111523 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109182, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109182, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25126 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109183 q = 1) : d111524 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109183, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109183, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109184 q = 1) : d111525 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109184, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109184, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109185 q = 1) : d111526 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109185, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109185, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109186 q = 1) : d111527 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109186, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109186, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109187 q = 1) : d111528 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109187, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109187, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25128 (p : Pattern) (ha : d107483 p = 1) (hb : d109192 p = 1) : d111533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11399 q = 1) (hb : d107483 q = 1) : d11399 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11400 q = 1) (hb : d107483 q = 1) : d111020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24800 q ha hb
    | true =>
      simp only [d11400, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11401 q = 1) (hb : d107483 q = 1) : d111021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11402 q = 1) (hb : d107483 q = 1) : d111022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11402, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11403 q = 1) (hb : d107483 q = 1) : d111023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11404 q = 1) (hb : d107483 q = 1) : d111024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109192 q = 1) : d111533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109192, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109192, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro25129 (p : Pattern) (ha : d107483 p = 1) (hb : d109203 p = 1) : d111544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11615 q = 1) (hb : d107483 q = 1) : d11615 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109198 q = 1) : d111539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109198, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24819 q hb ha
    | true =>
      simp only [d109198, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109199 q = 1) : d111540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109199, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109199, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109200 q = 1) : d111541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109200, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109200, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109201 q = 1) : d111542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109201, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109201, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109202 q = 1) : d111543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109202, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109202, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109203 q = 1) : d111544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109203, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109203, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25130 (p : Pattern) (ha : d107483 p = 1) (hb : d109209 p = 1) : d111550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11406 q = 1) (hb : d107483 q = 1) : d111026 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24799 q ha hb
    | true =>
      simp only [d11406, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24801 q ha hb
  have h2 (q : Pattern) (ha : d11407 q = 1) (hb : d107483 q = 1) : d111027 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11407, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109190 q = 1) : d111531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109190, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109190, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109191 q = 1) : d111532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109191, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109191, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109193 q = 1) : d111534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109193, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109193, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25128 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109194 q = 1) : d111535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109194, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109194, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109195 q = 1) : d111536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109195, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109195, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109196 q = 1) : d111537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109196, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109196, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109197 q = 1) : d111538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109197, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109197, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109204 q = 1) : d111545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109204, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109204, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25129 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109205 q = 1) : d111546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109205, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109205, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109206 q = 1) : d111547 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109206, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109206, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109207 q = 1) : d111548 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109207, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109207, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109208 q = 1) : d111549 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109208, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109208, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109209 q = 1) : d111550 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109209, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109209, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25131 (p : Pattern) (ha : d107483 p = 1) (hb : d109215 p = 1) : d111556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109210 q = 1) : d111551 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109210, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109210, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25130 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109211 q = 1) : d111552 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109211, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109211, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109212 q = 1) : d111553 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109212, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109212, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109213 q = 1) : d111554 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109213, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109213, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109214 q = 1) : d111555 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109214, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109214, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109215 q = 1) : d111556 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109215, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109215, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25132 (p : Pattern) (ha : d107483 p = 1) (hb : d109221 p = 1) : d111562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11670 q = 1) (hb : d107483 q = 1) : d11670 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11671 q = 1) (hb : d107483 q = 1) : d111154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24828 q ha hb
    | true =>
      simp only [d11671, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11672 q = 1) (hb : d107483 q = 1) : d111155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11673 q = 1) (hb : d107483 q = 1) : d111156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11673, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11674 q = 1) (hb : d107483 q = 1) : d111157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11675 q = 1) (hb : d107483 q = 1) : d111158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109221 q = 1) : d111562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109221, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109221, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro25133 (p : Pattern) (ha : d107483 p = 1) (hb : d109232 p = 1) : d111573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11886 q = 1) (hb : d107483 q = 1) : d11886 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109227 q = 1) : d111568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109227, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24847 q hb ha
    | true =>
      simp only [d109227, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109228 q = 1) : d111569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109228, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109228, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109229 q = 1) : d111570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109229, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109229, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109230 q = 1) : d111571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109230, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109230, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109231 q = 1) : d111572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109231, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109231, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109232 q = 1) : d111573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109232, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109232, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25134 (p : Pattern) (ha : d107483 p = 1) (hb : d109238 p = 1) : d111579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d107483 q = 1) : d111160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24827 q ha hb
    | true =>
      simp only [d11677, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24829 q ha hb
  have h2 (q : Pattern) (ha : d11678 q = 1) (hb : d107483 q = 1) : d111161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109219 q = 1) : d111560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109219, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109219, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109220 q = 1) : d111561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109220, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109220, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109222 q = 1) : d111563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109222, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109222, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25132 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109223 q = 1) : d111564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109223, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109223, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109224 q = 1) : d111565 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109224, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109224, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109225 q = 1) : d111566 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109225, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109225, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109226 q = 1) : d111567 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109226, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109226, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109233 q = 1) : d111574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109233, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109233, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25133 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109234 q = 1) : d111575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109234, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109234, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109235 q = 1) : d111576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109235, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109235, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109236 q = 1) : d111577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109236, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109236, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109237 q = 1) : d111578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109237, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109237, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109238 q = 1) : d111579 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109238, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109238, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25135 (p : Pattern) (ha : d107483 p = 1) (hb : d109244 p = 1) : d111585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109239 q = 1) : d111580 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109239, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109239, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25134 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109240 q = 1) : d111581 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109240, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109240, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109241 q = 1) : d111582 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109241, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109241, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109242 q = 1) : d111583 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109242, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109242, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109243 q = 1) : d111584 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109243, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109243, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109244 q = 1) : d111585 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109244, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109244, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25136 (p : Pattern) (ha : d107483 p = 1) (hb : d109251 p = 1) : d111592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11942 q = 1) (hb : d107483 q = 1) : d11942 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d11943 q = 1) (hb : d107483 q = 1) : d111289 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24856 q ha hb
    | true =>
      simp only [d11943, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11944 q = 1) (hb : d107483 q = 1) : d111290 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11944, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11945 q = 1) (hb : d107483 q = 1) : d111291 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11945, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11946 q = 1) (hb : d107483 q = 1) : d111292 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11947 q = 1) (hb : d107483 q = 1) : d111293 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109251 q = 1) : d111592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109251, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109251, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro25137 (p : Pattern) (ha : d107483 p = 1) (hb : d109262 p = 1) : d111603 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12158 q = 1) (hb : d107483 q = 1) : d12158 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109257 q = 1) : d111598 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109257, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24875 q hb ha
    | true =>
      simp only [d109257, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109258 q = 1) : d111599 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109258, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109258, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109259 q = 1) : d111600 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109259, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109259, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109260 q = 1) : d111601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109260, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109260, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109261 q = 1) : d111602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109261, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109261, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109262 q = 1) : d111603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109262, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109262, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro25138 (p : Pattern) (ha : d107483 p = 1) (hb : d109268 p = 1) : d111609 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d107483 q = 1) : d111295 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24855 q ha hb
    | true =>
      simp only [d11949, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24857 q ha hb
  have h2 (q : Pattern) (ha : d11950 q = 1) (hb : d107483 q = 1) : d111296 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109249 q = 1) : d111590 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109249, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d109249, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109250 q = 1) : d111591 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109250, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109250, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109252 q = 1) : d111593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109252, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109252, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25136 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109253 q = 1) : d111594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109253, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109253, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109254 q = 1) : d111595 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109254, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109254, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109255 q = 1) : d111596 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109255, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109255, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109256 q = 1) : d111597 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109256, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109256, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109263 q = 1) : d111604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109263, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109263, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25137 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109264 q = 1) : d111605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109264, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109264, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109265 q = 1) : d111606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109265, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109265, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109266 q = 1) : d111607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109266, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109266, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109267 q = 1) : d111608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109267, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109267, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109268 q = 1) : d111609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109268, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109268, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25139 (p : Pattern) (ha : d107483 p = 1) (hb : d109274 p = 1) : d111615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109269 q = 1) : d111610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109269, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109269, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25138 q ha hb
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109270 q = 1) : d111611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109270, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109270, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109271 q = 1) : d111612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109271, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109271, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109272 q = 1) : d111613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109272, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109272, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109273 q = 1) : d111614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109273, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109273, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109274 q = 1) : d111615 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109274, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109274, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25140 (p : Pattern) (ha : d107483 p = 1) (hb : d109280 p = 1) : d111621 p = 1 := by
  have h0 (q : Pattern) (ha : d107483 q = 1) (hb : d109161 q = 1) : d111502 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109161, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25119 q ha hb
    | true =>
      simp only [d109161, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25123 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109188 q = 1) : d111529 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109188, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109188, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25127 q ha hb
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109189 q = 1) : d111530 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109189, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109189, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109216 q = 1) : d111557 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109216, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109216, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25131 q ha hb
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109217 q = 1) : d111558 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109217, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109217, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109218 q = 1) : d111559 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109218, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109218, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107483 q = 1) (hb : d109245 q = 1) : d111586 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109245, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109245, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25135 q ha hb
  have h8 (q : Pattern) (ha : d107483 q = 1) (hb : d109246 q = 1) : d111587 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109246, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109246, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107483 q = 1) (hb : d109247 q = 1) : d111588 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109247, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109247, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107483 q = 1) (hb : d109248 q = 1) : d111589 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109248, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109248, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107483 q = 1) (hb : d109275 q = 1) : d111616 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109275, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109275, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25139 q ha hb
  have h12 (q : Pattern) (ha : d107483 q = 1) (hb : d109276 q = 1) : d111617 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109276, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109276, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107483 q = 1) (hb : d109277 q = 1) : d111618 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109277, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109277, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107483 q = 1) (hb : d109278 q = 1) : d111619 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109278, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109278, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107483 q = 1) (hb : d109279 q = 1) : d111620 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109279, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109279, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107483 q = 1) (hb : d109280 q = 1) : d111621 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109280, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109280, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro25141 (p : Pattern) (ha : d107483 p = 1) (hb : d109286 p = 1) : d111627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109281 q = 1) : d111622 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109281, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25140 q ha hb
    | true =>
      simp only [d109281, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109282 q = 1) : d111623 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109282, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109282, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109283 q = 1) : d111624 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109283, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109283, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109284 q = 1) : d111625 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109284, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109284, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109285 q = 1) : d111626 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109285, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109285, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109286 q = 1) : d111627 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109286, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109286, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25142 (p : Pattern) (ha : d107483 p = 1) (hb : d109292 p = 1) : d111633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109287 q = 1) : d111628 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109287, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25141 q ha hb
    | true =>
      simp only [d109287, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109288 q = 1) : d111629 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109288, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109288, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109289 q = 1) : d111630 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109289, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109289, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109290 q = 1) : d111631 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109290, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109290, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109291 q = 1) : d111632 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109291, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109291, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109292 q = 1) : d111633 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109292, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109292, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25143 (p : Pattern) (ha : d107483 p = 1) (hb : d109298 p = 1) : d111639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109293 q = 1) : d111634 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109293, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25142 q ha hb
    | true =>
      simp only [d109293, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109294 q = 1) : d111635 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109294, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109294, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109295 q = 1) : d111636 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109295, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109295, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109296 q = 1) : d111637 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109296, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109296, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109297 q = 1) : d111638 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109297, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109297, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109298 q = 1) : d111639 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109298, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109298, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25144 (p : Pattern) (ha : d107483 p = 1) (hb : d109304 p = 1) : d111645 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109299 q = 1) : d111640 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109299, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25143 q ha hb
    | true =>
      simp only [d109299, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109300 q = 1) : d111641 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109300, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109300, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109301 q = 1) : d111642 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109301, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109301, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109302 q = 1) : d111643 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109302, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109302, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109303 q = 1) : d111644 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109303, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109303, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109304 q = 1) : d111645 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109304, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109304, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25145 (p : Pattern) (ha : d107483 p = 1) (hb : d109310 p = 1) : d111651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109305 q = 1) : d111646 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109305, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25144 q ha hb
    | true =>
      simp only [d109305, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109306 q = 1) : d111647 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109306, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109306, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109307 q = 1) : d111648 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109307, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109307, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109308 q = 1) : d111649 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109308, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109308, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109309 q = 1) : d111650 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109309, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109309, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109310 q = 1) : d111651 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109310, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109310, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25146 (p : Pattern) (ha : d107483 p = 1) (hb : d109316 p = 1) : d111657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109311 q = 1) : d111652 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109311, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25145 q ha hb
    | true =>
      simp only [d109311, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109312 q = 1) : d111653 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109312, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109312, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109313 q = 1) : d111654 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109313, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109313, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109314 q = 1) : d111655 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109314, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109314, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109315 q = 1) : d111656 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109315, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109315, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109316 q = 1) : d111657 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109316, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109316, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25147 (p : Pattern) (ha : d107483 p = 1) (hb : d109322 p = 1) : d111663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107483 q = 1) (hb : d109317 q = 1) : d111658 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109317, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25146 q ha hb
    | true =>
      simp only [d109317, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d107483 q = 1) (hb : d109318 q = 1) : d111659 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109318, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109318, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d107483 q = 1) (hb : d109319 q = 1) : d111660 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109319, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109319, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d107483 q = 1) (hb : d109320 q = 1) : d111661 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109320, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109320, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d107483 q = 1) (hb : d109321 q = 1) : d111662 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109321, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109321, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d107483 q = 1) (hb : d109322 q = 1) : d111663 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109322, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109322, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25148 (p : Pattern) (ha : d83767 p = 1) (hb : d110638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83671 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
    | true =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d83757 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83757, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83764 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83764, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83765 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83765, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83766 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83766, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83767 q = 1) (hb : d110638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25149 (p : Pattern) (ha : d83786 p = 1) (hb : d110645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83671 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24890 q ha hb
    | true =>
      simp only [d83671, d110584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d83757 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83757, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d83764 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83764, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83765 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83765, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83766 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83766, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83772 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83776 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83678 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24892 q ha hb
    | true =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d83779 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83779, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83783 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83783, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83784 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d83784, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83785 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83785, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83786 q = 1) (hb : d110645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83786, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25150 (p : Pattern) (ha : d83795 p = 1) (hb : d111453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83678 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24892 q ha hb
    | true =>
      simp only [d83678, d110591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83779, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83783 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83793 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83794 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83795 q = 1) (hb : d111453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25151 (p : Pattern) (ha : d83820 p = 1) (hb : d111463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83704 q = 1) (hb : d110617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83704, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24896 q ha hb
    | true =>
      simp only [d83704, d110617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d111459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83810, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83817 q = 1) (hb : d111460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83818 q = 1) (hb : d111461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83819 q = 1) (hb : d111462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83820 q = 1) (hb : d111463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25152 (p : Pattern) (ha : d83826 p = 1) (hb : d111469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83787 q = 1) (hb : d110646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25148 q ha hb
    | true =>
      simp only [d83787, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25149 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83790 q = 1) (hb : d110647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83790, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83791 q = 1) (hb : d111451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83791, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83792 q = 1) (hb : d111452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83792, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83796 q = 1) (hb : d111454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83796, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25150 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83797 q = 1) (hb : d111455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83797, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83798 q = 1) (hb : d111456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83798, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83799 q = 1) (hb : d111457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83799, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83800 q = 1) (hb : d111458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83800, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83821 q = 1) (hb : d111464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83821, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25151 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83822 q = 1) (hb : d111465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83822, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83823 q = 1) (hb : d111466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83823, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83824 q = 1) (hb : d111467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83824, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83825 q = 1) (hb : d111468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83825, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83826 q = 1) (hb : d111469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83826, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25153 (p : Pattern) (ha : d83832 p = 1) (hb : d111475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d83716 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d83716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d83716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10167 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d83717 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d83717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d83717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d83718 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d83718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d83718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d83719 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d83719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d83719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d83720 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d83720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d83720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83827 q = 1) (hb : d111470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83827, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25152 q ha hb
  have h8 (q : Pattern) (ha : d83828 q = 1) (hb : d111471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83828, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83829 q = 1) (hb : d111472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83829, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83830 q = 1) (hb : d111473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83830, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83831 q = 1) (hb : d111474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83831, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83832 q = 1) (hb : d111475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d83832, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro25154 (p : Pattern) (ha : d83886 p = 1) (hb : d110755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83837 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24928 q ha hb
    | true =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q hb ha
  have h5 (q : Pattern) (ha : d83876 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83876, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83883 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83883, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83884 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83884, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83885 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83885, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83886 q = 1) (hb : d110755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83886, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83886, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25155 (p : Pattern) (ha : d83905 p = 1) (hb : d110764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83837 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24928 q ha hb
    | true =>
      simp only [d83837, d110750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24921 q hb ha
  have h4 (q : Pattern) (ha : d83876 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83876, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d83883 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83883, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83884 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83884, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83885 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83885, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83891 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83895 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83846 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24930 q ha hb
    | true =>
      simp only [d83846, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q hb ha
  have h13 (q : Pattern) (ha : d83898 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83898, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83902 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83902, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83903 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83903, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d83903, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83904 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83904, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83904, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83905 q = 1) (hb : d110764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83905, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83905, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25156 (p : Pattern) (ha : d83914 p = 1) (hb : d111478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83846 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24930 q ha hb
    | true =>
      simp only [d83846, d110759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24922 q hb ha
  have h3 (q : Pattern) (ha : d83898 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83898, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83902 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83902, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83912 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83912, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83912, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83913 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83913, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83913, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83914 q = 1) (hb : d111478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25157 (p : Pattern) (ha : d83944 p = 1) (hb : d111489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83932 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83933 q = 1) (hb : d111484 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83933, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24951 q ha hb
    | true =>
      simp only [d83933, d111484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24926 q hb ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d111485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83934, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83940 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83941 q = 1) (hb : d111486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83942 q = 1) (hb : d111487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83943 q = 1) (hb : d111488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83944 q = 1) (hb : d111489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25158 (p : Pattern) (ha : d83950 p = 1) (hb : d111495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83906 q = 1) (hb : d110765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83906, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25154 q ha hb
    | true =>
      simp only [d83906, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25155 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83909 q = 1) (hb : d110766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83909, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83909, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83910 q = 1) (hb : d111476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83910, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83911 q = 1) (hb : d111477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83911, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83915 q = 1) (hb : d111479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83915, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25156 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83916 q = 1) (hb : d111480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83916, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83917 q = 1) (hb : d111481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83917, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83918 q = 1) (hb : d111482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83918, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83919 q = 1) (hb : d111483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83919, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83945 q = 1) (hb : d111490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83945, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25157 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83946 q = 1) (hb : d111491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83946, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83947 q = 1) (hb : d111492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83947, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83948 q = 1) (hb : d111493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83948, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83949 q = 1) (hb : d111494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83949, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83950 q = 1) (hb : d111495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83950, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25159 (p : Pattern) (ha : d83956 p = 1) (hb : d111501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d111496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25158 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d111497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d111498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d111499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d111500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d111501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25160 (p : Pattern) (ha : d84015 p = 1) (hb : d110883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83966 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24965 q ha hb
    | true =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q hb ha
  have h5 (q : Pattern) (ha : d84005 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84005, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84012 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84012, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84013 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84013, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84014 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84014, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84015 q = 1) (hb : d110883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84015, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84015, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25161 (p : Pattern) (ha : d84034 p = 1) (hb : d110892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83966 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24965 q ha hb
    | true =>
      simp only [d83966, d110878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24957 q hb ha
  have h4 (q : Pattern) (ha : d84005 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84005, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84012 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84012, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84013 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84013, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84014 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84014, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84020 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83975 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24967 q ha hb
    | true =>
      simp only [d83975, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q hb ha
  have h13 (q : Pattern) (ha : d84027 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84027, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84031 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84031, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84032 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84032, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84032, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84033 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84033, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84033, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84034 q = 1) (hb : d110892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84034, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84034, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25162 (p : Pattern) (ha : d84043 p = 1) (hb : d111505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83975 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24967 q ha hb
    | true =>
      simp only [d83975, d110887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24958 q hb ha
  have h3 (q : Pattern) (ha : d84027 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84027, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84031 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84031, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84041 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84041, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84041, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84042 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84042, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84042, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84043 q = 1) (hb : d111505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25163 (p : Pattern) (ha : d84077 p = 1) (hb : d111516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84066 q = 1) (hb : d111511 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84066, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24989 q ha hb
    | true =>
      simp only [d84066, d111511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24962 q hb ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d111512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84067, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84073 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84074 q = 1) (hb : d111513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84075 q = 1) (hb : d111514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84076 q = 1) (hb : d111515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84077 q = 1) (hb : d111516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25164 (p : Pattern) (ha : d84083 p = 1) (hb : d111522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84035 q = 1) (hb : d110893 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84035, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25160 q ha hb
    | true =>
      simp only [d84035, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25161 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84038 q = 1) (hb : d110894 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84038, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84038, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84039 q = 1) (hb : d111503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84039, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84040 q = 1) (hb : d111504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84040, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84044 q = 1) (hb : d111506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84044, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25162 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84045 q = 1) (hb : d111507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84045, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84046 q = 1) (hb : d111508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84046, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84047 q = 1) (hb : d111509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84047, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84048 q = 1) (hb : d111510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84048, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84078 q = 1) (hb : d111517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84078, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25163 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84079 q = 1) (hb : d111518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84079, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84080 q = 1) (hb : d111519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84080, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84081 q = 1) (hb : d111520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84081, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84082 q = 1) (hb : d111521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84082, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84083 q = 1) (hb : d111522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84083, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25165 (p : Pattern) (ha : d84089 p = 1) (hb : d111528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d111523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25164 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d111524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d111525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d111526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d111527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d111528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25166 (p : Pattern) (ha : d84149 p = 1) (hb : d111016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84100 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25003 q ha hb
    | true =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q hb ha
  have h5 (q : Pattern) (ha : d84139 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84139, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84146 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84146, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84147 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84147, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84148 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84148, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84149 q = 1) (hb : d111016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84149, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84149, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25167 (p : Pattern) (ha : d84168 p = 1) (hb : d111025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84100 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25003 q ha hb
    | true =>
      simp only [d84100, d111011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24995 q hb ha
  have h4 (q : Pattern) (ha : d84139 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84139, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84146 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84146, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84147 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84147, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84148 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84148, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84154 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84158 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84109 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25005 q ha hb
    | true =>
      simp only [d84109, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q hb ha
  have h13 (q : Pattern) (ha : d84161 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84161, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84165 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84165, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84166 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84166, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84166, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84167 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84167, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84167, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84168 q = 1) (hb : d111025 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84168, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84168, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25168 (p : Pattern) (ha : d84177 p = 1) (hb : d111533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84109 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25005 q ha hb
    | true =>
      simp only [d84109, d111020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24996 q hb ha
  have h3 (q : Pattern) (ha : d84161 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84161, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84165 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84165, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84175 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84175, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84175, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84176 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84176, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84176, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84177 q = 1) (hb : d111533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25169 (p : Pattern) (ha : d84211 p = 1) (hb : d111544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84199 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84200 q = 1) (hb : d111539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84200, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25027 q ha hb
    | true =>
      simp only [d84200, d111539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25000 q hb ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d111540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84201, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84208 q = 1) (hb : d111541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84209 q = 1) (hb : d111542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84210 q = 1) (hb : d111543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84211 q = 1) (hb : d111544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25170 (p : Pattern) (ha : d84217 p = 1) (hb : d111550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84117 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84169 q = 1) (hb : d111026 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84169, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25166 q ha hb
    | true =>
      simp only [d84169, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25167 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84172 q = 1) (hb : d111027 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84172, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84172, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84173 q = 1) (hb : d111531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84173, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84174 q = 1) (hb : d111532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84174, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84178 q = 1) (hb : d111534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84178, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25168 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84179 q = 1) (hb : d111535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84179, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84180 q = 1) (hb : d111536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84180, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84181 q = 1) (hb : d111537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84181, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84182 q = 1) (hb : d111538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84182, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84212 q = 1) (hb : d111545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84212, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25169 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84213 q = 1) (hb : d111546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84213, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84214 q = 1) (hb : d111547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84214, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84215 q = 1) (hb : d111548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84215, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84216 q = 1) (hb : d111549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84216, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84217 q = 1) (hb : d111550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84217, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25171 (p : Pattern) (ha : d84223 p = 1) (hb : d111556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d111551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25170 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d111552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d111553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d111554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d111555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d111556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25172 (p : Pattern) (ha : d84284 p = 1) (hb : d111150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84235 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25041 q ha hb
    | true =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q hb ha
  have h5 (q : Pattern) (ha : d84274 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84274, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84281 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84281, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84282 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84282, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84283 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84283, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84284 q = 1) (hb : d111150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84284, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84284, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25173 (p : Pattern) (ha : d84303 p = 1) (hb : d111159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84235 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25041 q ha hb
    | true =>
      simp only [d84235, d111145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25033 q hb ha
  have h4 (q : Pattern) (ha : d84274 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84274, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84281 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84281, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84282 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84282, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84283 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84283, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84293 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84244 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25043 q ha hb
    | true =>
      simp only [d84244, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q hb ha
  have h13 (q : Pattern) (ha : d84296 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84296, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84300 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84300, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84301 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84301, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84301, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84302 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84302, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84302, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84303 q = 1) (hb : d111159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84303, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84303, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25174 (p : Pattern) (ha : d84312 p = 1) (hb : d111562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84244 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25043 q ha hb
    | true =>
      simp only [d84244, d111154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25034 q hb ha
  have h3 (q : Pattern) (ha : d84296 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84296, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84300 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84300, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84310 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84310, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84310, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84311 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84311, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84311, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84312 q = 1) (hb : d111562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25175 (p : Pattern) (ha : d84346 p = 1) (hb : d111573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84335 q = 1) (hb : d111568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84335, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25065 q ha hb
    | true =>
      simp only [d84335, d111568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25038 q hb ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d111569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84336, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84343 q = 1) (hb : d111570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84344 q = 1) (hb : d111571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84345 q = 1) (hb : d111572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84346 q = 1) (hb : d111573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25176 (p : Pattern) (ha : d84352 p = 1) (hb : d111579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84304 q = 1) (hb : d111160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84304, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25172 q ha hb
    | true =>
      simp only [d84304, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25173 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84307 q = 1) (hb : d111161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84307, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84307, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84308 q = 1) (hb : d111560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84308, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84309 q = 1) (hb : d111561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84309, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84313 q = 1) (hb : d111563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84313, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25174 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84314 q = 1) (hb : d111564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84314, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84315 q = 1) (hb : d111565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84315, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84316 q = 1) (hb : d111566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84316, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84317 q = 1) (hb : d111567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84317, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84347 q = 1) (hb : d111574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84347, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25175 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84348 q = 1) (hb : d111575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84348, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84349 q = 1) (hb : d111576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84349, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84350 q = 1) (hb : d111577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84350, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84351 q = 1) (hb : d111578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84351, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84352 q = 1) (hb : d111579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84352, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25177 (p : Pattern) (ha : d84358 p = 1) (hb : d111585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d111580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25176 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d111581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d111582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d111583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d111584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d111585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25178 (p : Pattern) (ha : d84420 p = 1) (hb : d111285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84371 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25079 q ha hb
    | true =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q hb ha
  have h5 (q : Pattern) (ha : d84410 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84410, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84417 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84417, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84418 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84418, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84419 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84419, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84420 q = 1) (hb : d111285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84420, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84420, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25179 (p : Pattern) (ha : d84439 p = 1) (hb : d111294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84371 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25079 q ha hb
    | true =>
      simp only [d84371, d111280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25071 q hb ha
  have h4 (q : Pattern) (ha : d84410 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84410, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84417 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84417, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84418 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84418, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84419 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84419, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84425 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84380 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25081 q ha hb
    | true =>
      simp only [d84380, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q hb ha
  have h13 (q : Pattern) (ha : d84432 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84432, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84436 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84436, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84437 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84437, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84437, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84438 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84438, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84438, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84439 q = 1) (hb : d111294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84439, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84439, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25180 (p : Pattern) (ha : d84448 p = 1) (hb : d111592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84380 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25081 q ha hb
    | true =>
      simp only [d84380, d111289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25072 q hb ha
  have h3 (q : Pattern) (ha : d84432 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84432, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84436 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84436, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84446 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84446, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84446, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84447 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84447, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84447, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84448 q = 1) (hb : d111592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25181 (p : Pattern) (ha : d84482 p = 1) (hb : d111603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84470 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84471 q = 1) (hb : d111598 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84471, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25103 q ha hb
    | true =>
      simp only [d84471, d111598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25076 q hb ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d111599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84472, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84479 q = 1) (hb : d111600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84480 q = 1) (hb : d111601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84481 q = 1) (hb : d111602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84482 q = 1) (hb : d111603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25182 (p : Pattern) (ha : d84488 p = 1) (hb : d111609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84440 q = 1) (hb : d111295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84440, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25178 q ha hb
    | true =>
      simp only [d84440, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25179 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84443 q = 1) (hb : d111296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84443, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84443, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84444 q = 1) (hb : d111590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84444, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84445 q = 1) (hb : d111591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84445, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84449 q = 1) (hb : d111593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84449, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25180 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84450 q = 1) (hb : d111594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84450, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84451 q = 1) (hb : d111595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84451, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84452 q = 1) (hb : d111596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84452, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84453 q = 1) (hb : d111597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84453, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84483 q = 1) (hb : d111604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84483, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25181 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84484 q = 1) (hb : d111605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84484, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84485 q = 1) (hb : d111606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84485, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84486 q = 1) (hb : d111607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84486, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84487 q = 1) (hb : d111608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84487, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84488 q = 1) (hb : d111609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84488, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25183 (p : Pattern) (ha : d84494 p = 1) (hb : d111615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d111610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25182 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d111611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d111612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d111613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d111614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d111615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25184 (p : Pattern) (ha : d84500 p = 1) (hb : d111621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d111502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25153 q ha hb
    | true =>
      simp only [d83957, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25159 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d111529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25165 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d111530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d111557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25171 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d111558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d111559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d111586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25177 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d111587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d111588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d111589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d111616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25183 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d111617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d111618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d111619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d111620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d111621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro25185 (p : Pattern) (ha : d84506 p = 1) (hb : d111627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d111622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25184 q ha hb
    | true =>
      simp only [d84501, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d111623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d111624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d111625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d111626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d111627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25186 (p : Pattern) (ha : d84512 p = 1) (hb : d111633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d111628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25185 q ha hb
    | true =>
      simp only [d84507, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d111629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d111630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d111631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d111632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d111633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25187 (p : Pattern) (ha : d84518 p = 1) (hb : d111639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d111634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25186 q ha hb
    | true =>
      simp only [d84513, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d111635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d111636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d111637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d111638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d111639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25188 (p : Pattern) (ha : d84524 p = 1) (hb : d111645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d111640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25187 q ha hb
    | true =>
      simp only [d84519, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d111641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d111642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d111643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d111644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d111645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25189 (p : Pattern) (ha : d84530 p = 1) (hb : d111651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d111646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25188 q ha hb
    | true =>
      simp only [d84525, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d111647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d111648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d111649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d111650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d111651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25190 (p : Pattern) (ha : d84536 p = 1) (hb : d111657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d111652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25189 q ha hb
    | true =>
      simp only [d84531, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d111653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d111654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d111655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d111656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d111657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25191 (p : Pattern) (ha : d84542 p = 1) (hb : d111663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d111658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25190 q ha hb
    | true =>
      simp only [d84537, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d111659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d111660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d111661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d111662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d111663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro25192 (p : Pattern) (ha : d85432 p = 1) (hb : d110638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85428 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85428, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85429 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85429, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85430 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85430, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85431 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85431, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85432 q = 1) (hb : d110638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85432, d110638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25193 (p : Pattern) (ha : d85437 p = 1) (hb : d110645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d110584 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85428 q = 1) (hb : d110634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85428, d110634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85429 q = 1) (hb : d110635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85429, d110635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85430 q = 1) (hb : d110636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85430, d110636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85431 q = 1) (hb : d110637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85431, d110637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7358 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7362 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85433 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85433, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85434 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85434, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85435 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85435, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85436 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85436, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85437 q = 1) (hb : d110645 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85437, d110645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25194 (p : Pattern) (ha : d85444 p = 1) (hb : d111453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110591 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85433 q = 1) (hb : d110641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85433, d110641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85434 q = 1) (hb : d110642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85434, d110642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85442 q = 1) (hb : d110643 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85442, d110643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85443 q = 1) (hb : d110644 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85443, d110644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85444 q = 1) (hb : d111453 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85444, d111453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25195 (p : Pattern) (ha : d85454 p = 1) (hb : d111463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110617 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85450 q = 1) (hb : d111459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85450, d111459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85451 q = 1) (hb : d111460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85451, d111460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85452 q = 1) (hb : d111461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85452, d111461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85453 q = 1) (hb : d111462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85453, d111462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85454 q = 1) (hb : d111463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85454, d111463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25196 (p : Pattern) (ha : d85460 p = 1) (hb : d111469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85438 q = 1) (hb : d110646 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25192 q ha hb
    | true =>
      simp only [d85438, d110646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25193 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85439 q = 1) (hb : d110647 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85439, d110647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85440 q = 1) (hb : d111451 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85440, d111451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85441 q = 1) (hb : d111452 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85441, d111452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85445 q = 1) (hb : d111454 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85445, d111454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25194 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85446 q = 1) (hb : d111455 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85446, d111455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85447 q = 1) (hb : d111456 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85447, d111456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85448 q = 1) (hb : d111457 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85448, d111457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85449 q = 1) (hb : d111458 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85449, d111458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85455 q = 1) (hb : d111464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85455, d111464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25195 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85456 q = 1) (hb : d111465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85456, d111465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85457 q = 1) (hb : d111466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85457, d111466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85458 q = 1) (hb : d111467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85458, d111467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85459 q = 1) (hb : d111468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85459, d111468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85460 q = 1) (hb : d111469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85460, d111469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25197 (p : Pattern) (ha : d85466 p = 1) (hb : d111475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d85423 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10216 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d85424 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d85425 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d85426 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d85427 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85461 q = 1) (hb : d111470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85461, d111470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25196 q ha hb
  have h8 (q : Pattern) (ha : d85462 q = 1) (hb : d111471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85462, d111471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85463 q = 1) (hb : d111472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85463, d111472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85464 q = 1) (hb : d111473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85464, d111473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85465 q = 1) (hb : d111474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85465, d111474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85466 q = 1) (hb : d111475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d85466, d111475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro25198 (p : Pattern) (ha : d85471 p = 1) (hb : d110755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85467 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85467, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85468 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85468, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85469 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85469, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85470 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85470, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85471 q = 1) (hb : d110755 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85471, d110755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25199 (p : Pattern) (ha : d85476 p = 1) (hb : d110764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d110750 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85467 q = 1) (hb : d110751 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85467, d110751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85468 q = 1) (hb : d110752 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85468, d110752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85469 q = 1) (hb : d110753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85469, d110753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85470 q = 1) (hb : d110754 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85470, d110754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7501 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85472 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85472, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85473 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85473, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85474 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85474, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85475 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85475, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85476 q = 1) (hb : d110764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85476, d110764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25200 (p : Pattern) (ha : d85483 p = 1) (hb : d111478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110759 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85472 q = 1) (hb : d110760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85472, d110760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85473 q = 1) (hb : d110761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85473, d110761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85481 q = 1) (hb : d110762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85481, d110762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85482 q = 1) (hb : d110763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85482, d110763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85483 q = 1) (hb : d111478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85483, d111478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25201 (p : Pattern) (ha : d85493 p = 1) (hb : d111489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111484 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85489 q = 1) (hb : d111485 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85489, d111485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85490 q = 1) (hb : d111486 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85490, d111486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85491 q = 1) (hb : d111487 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85491, d111487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85492 q = 1) (hb : d111488 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85492, d111488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85493 q = 1) (hb : d111489 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85493, d111489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25202 (p : Pattern) (ha : d85499 p = 1) (hb : d111495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7451 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85477 q = 1) (hb : d110765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25198 q ha hb
    | true =>
      simp only [d85477, d110765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25199 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7516 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85478 q = 1) (hb : d110766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85478, d110766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85479 q = 1) (hb : d111476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85479, d111476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85480 q = 1) (hb : d111477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85480, d111477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85484 q = 1) (hb : d111479 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85484, d111479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25200 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85485 q = 1) (hb : d111480 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85485, d111480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85486 q = 1) (hb : d111481 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85486, d111481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85487 q = 1) (hb : d111482 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85487, d111482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85488 q = 1) (hb : d111483 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85488, d111483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85494 q = 1) (hb : d111490 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85494, d111490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25201 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85495 q = 1) (hb : d111491 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85495, d111491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85496 q = 1) (hb : d111492 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85496, d111492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85497 q = 1) (hb : d111493 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85497, d111493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85498 q = 1) (hb : d111494 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85498, d111494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85499 q = 1) (hb : d111495 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85499, d111495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25203 (p : Pattern) (ha : d85505 p = 1) (hb : d111501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85500 q = 1) (hb : d111496 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85500, d111496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25202 q ha hb
  have h2 (q : Pattern) (ha : d85501 q = 1) (hb : d111497 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85501, d111497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85502 q = 1) (hb : d111498 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85502, d111498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85503 q = 1) (hb : d111499 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85503, d111499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85504 q = 1) (hb : d111500 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85504, d111500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85505 q = 1) (hb : d111501 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85505, d111501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25204 (p : Pattern) (ha : d85511 p = 1) (hb : d110883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85507 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85507, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85508 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85508, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85509 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85509, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85510 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85510, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85511 q = 1) (hb : d110883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85511, d110883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25205 (p : Pattern) (ha : d85516 p = 1) (hb : d110892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d110878 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85507 q = 1) (hb : d110879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85507, d110879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85508 q = 1) (hb : d110880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85508, d110880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85509 q = 1) (hb : d110881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85509, d110881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85510 q = 1) (hb : d110882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85510, d110882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7645 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7649 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85512 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85512, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85513 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85513, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85514 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85514, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85515 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85515, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85516 q = 1) (hb : d110892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85516, d110892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25206 (p : Pattern) (ha : d85523 p = 1) (hb : d111505 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d110887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85512 q = 1) (hb : d110888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85512, d110888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85513 q = 1) (hb : d110889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85513, d110889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85521 q = 1) (hb : d110890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85521, d110890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85522 q = 1) (hb : d110891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85522, d110891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85523 q = 1) (hb : d111505 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85523, d111505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25207 (p : Pattern) (ha : d85533 p = 1) (hb : d111516 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7692 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111511 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85529 q = 1) (hb : d111512 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85529, d111512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85530 q = 1) (hb : d111513 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85530, d111513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85531 q = 1) (hb : d111514 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85531, d111514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85532 q = 1) (hb : d111515 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85532, d111515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85533 q = 1) (hb : d111516 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85533, d111516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25208 (p : Pattern) (ha : d85539 p = 1) (hb : d111522 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85517 q = 1) (hb : d110893 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25204 q ha hb
    | true =>
      simp only [d85517, d110893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25205 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85518 q = 1) (hb : d110894 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85518, d110894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85519 q = 1) (hb : d111503 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85519, d111503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85520 q = 1) (hb : d111504 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85520, d111504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85524 q = 1) (hb : d111506 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85524, d111506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25206 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85525 q = 1) (hb : d111507 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85525, d111507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85526 q = 1) (hb : d111508 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85526, d111508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85527 q = 1) (hb : d111509 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85527, d111509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85528 q = 1) (hb : d111510 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85528, d111510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85534 q = 1) (hb : d111517 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85534, d111517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25207 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85535 q = 1) (hb : d111518 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85535, d111518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85536 q = 1) (hb : d111519 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85536, d111519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85537 q = 1) (hb : d111520 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85537, d111520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85538 q = 1) (hb : d111521 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85538, d111521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85539 q = 1) (hb : d111522 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85539, d111522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25209 (p : Pattern) (ha : d85545 p = 1) (hb : d111528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85540 q = 1) (hb : d111523 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85540, d111523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25208 q ha hb
  have h2 (q : Pattern) (ha : d85541 q = 1) (hb : d111524 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85541, d111524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85542 q = 1) (hb : d111525 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85542, d111525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85543 q = 1) (hb : d111526 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85543, d111526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85544 q = 1) (hb : d111527 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85544, d111527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85545 q = 1) (hb : d111528 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85545, d111528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25210 (p : Pattern) (ha : d85552 p = 1) (hb : d111016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85548 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85548, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85549 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85549, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85550 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85550, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85551 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85551, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85552 q = 1) (hb : d111016 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85552, d111016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25211 (p : Pattern) (ha : d85557 p = 1) (hb : d111025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111011 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85548 q = 1) (hb : d111012 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85548, d111012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85549 q = 1) (hb : d111013 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85549, d111013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85550 q = 1) (hb : d111014 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85550, d111014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85551 q = 1) (hb : d111015 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85551, d111015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7798 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7802 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85553 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85553, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85554 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85554, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85555 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85555, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85556 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85556, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85557 q = 1) (hb : d111025 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85557, d111025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25212 (p : Pattern) (ha : d85564 p = 1) (hb : d111533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111020 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85553 q = 1) (hb : d111021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85553, d111021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85554 q = 1) (hb : d111022 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85554, d111022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85562 q = 1) (hb : d111023 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85562, d111023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85563 q = 1) (hb : d111024 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85563, d111024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85564 q = 1) (hb : d111533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85564, d111533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25213 (p : Pattern) (ha : d85574 p = 1) (hb : d111544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85570 q = 1) (hb : d111540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85570, d111540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7861 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85571 q = 1) (hb : d111541 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85571, d111541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85572 q = 1) (hb : d111542 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85572, d111542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85573 q = 1) (hb : d111543 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85573, d111543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85574 q = 1) (hb : d111544 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85574, d111544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25214 (p : Pattern) (ha : d85580 p = 1) (hb : d111550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85558 q = 1) (hb : d111026 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25210 q ha hb
    | true =>
      simp only [d85558, d111026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25211 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85559 q = 1) (hb : d111027 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85559, d111027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85560 q = 1) (hb : d111531 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85560, d111531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85561 q = 1) (hb : d111532 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85561, d111532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85565 q = 1) (hb : d111534 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85565, d111534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25212 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85566 q = 1) (hb : d111535 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85566, d111535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85567 q = 1) (hb : d111536 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85567, d111536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85568 q = 1) (hb : d111537 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85568, d111537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85569 q = 1) (hb : d111538 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85569, d111538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85575 q = 1) (hb : d111545 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85575, d111545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25213 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85576 q = 1) (hb : d111546 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85576, d111546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85577 q = 1) (hb : d111547 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85577, d111547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85578 q = 1) (hb : d111548 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85578, d111548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85579 q = 1) (hb : d111549 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85579, d111549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85580 q = 1) (hb : d111550 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85580, d111550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25215 (p : Pattern) (ha : d85586 p = 1) (hb : d111556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85581 q = 1) (hb : d111551 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85581, d111551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25214 q ha hb
  have h2 (q : Pattern) (ha : d85582 q = 1) (hb : d111552 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85582, d111552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85583 q = 1) (hb : d111553 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85583, d111553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85584 q = 1) (hb : d111554 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85584, d111554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85585 q = 1) (hb : d111555 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85585, d111555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85586 q = 1) (hb : d111556 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85586, d111556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25216 (p : Pattern) (ha : d85594 p = 1) (hb : d111150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85590 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85590, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85591 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85591, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85592 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85592, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85593 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85593, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85594 q = 1) (hb : d111150 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85594, d111150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25217 (p : Pattern) (ha : d85599 p = 1) (hb : d111159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111145 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85590 q = 1) (hb : d111146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85590, d111146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85591 q = 1) (hb : d111147 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85591, d111147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85592 q = 1) (hb : d111148 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85592, d111148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85593 q = 1) (hb : d111149 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85593, d111149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7956 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85595 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85595, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85596 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85596, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85597 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85597, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85598 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85598, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85599 q = 1) (hb : d111159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85599, d111159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25218 (p : Pattern) (ha : d85606 p = 1) (hb : d111562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85595 q = 1) (hb : d111155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85595, d111155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85596 q = 1) (hb : d111156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85596, d111156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85604 q = 1) (hb : d111157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85604, d111157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85605 q = 1) (hb : d111158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85605, d111158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85606 q = 1) (hb : d111562 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85606, d111562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25219 (p : Pattern) (ha : d85616 p = 1) (hb : d111573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111568 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85612 q = 1) (hb : d111569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85612, d111569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85613 q = 1) (hb : d111570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85613, d111570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85614 q = 1) (hb : d111571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85614, d111571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85615 q = 1) (hb : d111572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85615, d111572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85616 q = 1) (hb : d111573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85616, d111573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25220 (p : Pattern) (ha : d85622 p = 1) (hb : d111579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85600 q = 1) (hb : d111160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25216 q ha hb
    | true =>
      simp only [d85600, d111160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25217 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7971 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85601 q = 1) (hb : d111161 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85601, d111161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85602 q = 1) (hb : d111560 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85602, d111560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85603 q = 1) (hb : d111561 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85603, d111561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85607 q = 1) (hb : d111563 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85607, d111563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25218 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85608 q = 1) (hb : d111564 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85608, d111564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85609 q = 1) (hb : d111565 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85609, d111565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85610 q = 1) (hb : d111566 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85610, d111566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85611 q = 1) (hb : d111567 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85611, d111567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85617 q = 1) (hb : d111574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85617, d111574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25219 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85618 q = 1) (hb : d111575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85618, d111575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85619 q = 1) (hb : d111576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85619, d111576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85620 q = 1) (hb : d111577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85620, d111577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85621 q = 1) (hb : d111578 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85621, d111578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85622 q = 1) (hb : d111579 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85622, d111579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25221 (p : Pattern) (ha : d85628 p = 1) (hb : d111585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85623 q = 1) (hb : d111580 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85623, d111580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25220 q ha hb
  have h2 (q : Pattern) (ha : d85624 q = 1) (hb : d111581 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85624, d111581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85625 q = 1) (hb : d111582 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85625, d111582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85626 q = 1) (hb : d111583 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85626, d111583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85627 q = 1) (hb : d111584 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85627, d111584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85628 q = 1) (hb : d111585 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85628, d111585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25222 (p : Pattern) (ha : d85637 p = 1) (hb : d111285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85633 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85633, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85634 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85634, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85635 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85635, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85636 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85636, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85637 q = 1) (hb : d111285 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85637, d111285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro25223 (p : Pattern) (ha : d85642 p = 1) (hb : d111294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111280 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85633 q = 1) (hb : d111281 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85633, d111281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85634 q = 1) (hb : d111282 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85634, d111282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85635 q = 1) (hb : d111283 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85635, d111283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85636 q = 1) (hb : d111284 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85636, d111284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8107 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8111 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85638 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85638, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85639 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85639, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85640 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85640, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85641 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85641, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85642 q = 1) (hb : d111294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85642, d111294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro25224 (p : Pattern) (ha : d85649 p = 1) (hb : d111592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111289 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85638 q = 1) (hb : d111290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85638, d111290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85639 q = 1) (hb : d111291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85639, d111291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85647 q = 1) (hb : d111292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85647, d111292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85648 q = 1) (hb : d111293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85648, d111293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85649 q = 1) (hb : d111592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85649, d111592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25225 (p : Pattern) (ha : d85659 p = 1) (hb : d111603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111598 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85655 q = 1) (hb : d111599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85655, d111599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85656 q = 1) (hb : d111600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85656, d111600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85657 q = 1) (hb : d111601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85657, d111601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85658 q = 1) (hb : d111602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85658, d111602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85659 q = 1) (hb : d111603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85659, d111603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25226 (p : Pattern) (ha : d85665 p = 1) (hb : d111609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8061 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85643 q = 1) (hb : d111295 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25222 q ha hb
    | true =>
      simp only [d85643, d111295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25223 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85644 q = 1) (hb : d111296 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85644, d111296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85645 q = 1) (hb : d111590 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85645, d111590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85646 q = 1) (hb : d111591 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85646, d111591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85650 q = 1) (hb : d111593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85650, d111593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25224 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85651 q = 1) (hb : d111594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85651, d111594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85652 q = 1) (hb : d111595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85652, d111595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85653 q = 1) (hb : d111596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85653, d111596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85654 q = 1) (hb : d111597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85654, d111597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85660 q = 1) (hb : d111604 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85660, d111604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25225 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85661 q = 1) (hb : d111605 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85661, d111605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85662 q = 1) (hb : d111606 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85662, d111606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85663 q = 1) (hb : d111607 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85663, d111607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85664 q = 1) (hb : d111608 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85664, d111608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85665 q = 1) (hb : d111609 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85665, d111609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro25227 (p : Pattern) (ha : d85671 p = 1) (hb : d111615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85666 q = 1) (hb : d111610 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85666, d111610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25226 q ha hb
  have h2 (q : Pattern) (ha : d85667 q = 1) (hb : d111611 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85667, d111611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85668 q = 1) (hb : d111612 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85668, d111612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85669 q = 1) (hb : d111613 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85669, d111613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85670 q = 1) (hb : d111614 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85670, d111614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85671 q = 1) (hb : d111615 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85671, d111615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25228 (p : Pattern) (ha : d85677 p = 1) (hb : d111621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d85506 q = 1) (hb : d111502 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25197 q ha hb
    | true =>
      simp only [d85506, d111502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25203 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85546 q = 1) (hb : d111529 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85546, d111529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25209 q ha hb
  have h3 (q : Pattern) (ha : d85547 q = 1) (hb : d111530 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d111530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85587 q = 1) (hb : d111557 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85587, d111557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25215 q ha hb
  have h5 (q : Pattern) (ha : d85588 q = 1) (hb : d111558 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85588, d111558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85589 q = 1) (hb : d111559 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d111559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85629 q = 1) (hb : d111586 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85629, d111586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25221 q ha hb
  have h8 (q : Pattern) (ha : d85630 q = 1) (hb : d111587 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85630, d111587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85631 q = 1) (hb : d111588 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85631, d111588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85632 q = 1) (hb : d111589 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d111589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85672 q = 1) (hb : d111616 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85672, d111616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25227 q ha hb
  have h12 (q : Pattern) (ha : d85673 q = 1) (hb : d111617 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85673, d111617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85674 q = 1) (hb : d111618 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85674, d111618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85675 q = 1) (hb : d111619 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85675, d111619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85676 q = 1) (hb : d111620 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d111620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85677 q = 1) (hb : d111621 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d111621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro25229 (p : Pattern) (ha : d85683 p = 1) (hb : d111627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85678 q = 1) (hb : d111622 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25228 q ha hb
    | true =>
      simp only [d85678, d111622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85679 q = 1) (hb : d111623 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d111623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85680 q = 1) (hb : d111624 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d111624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85681 q = 1) (hb : d111625 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d111625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85682 q = 1) (hb : d111626 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d111626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85683 q = 1) (hb : d111627 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d111627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25230 (p : Pattern) (ha : d85689 p = 1) (hb : d111633 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85684 q = 1) (hb : d111628 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25229 q ha hb
    | true =>
      simp only [d85684, d111628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85685 q = 1) (hb : d111629 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d111629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85686 q = 1) (hb : d111630 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d111630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85687 q = 1) (hb : d111631 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d111631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85688 q = 1) (hb : d111632 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d111632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85689 q = 1) (hb : d111633 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d111633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25231 (p : Pattern) (ha : d85695 p = 1) (hb : d111639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85690 q = 1) (hb : d111634 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25230 q ha hb
    | true =>
      simp only [d85690, d111634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85691 q = 1) (hb : d111635 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d111635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85692 q = 1) (hb : d111636 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d111636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85693 q = 1) (hb : d111637 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d111637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85694 q = 1) (hb : d111638 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d111638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85695 q = 1) (hb : d111639 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d111639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25232 (p : Pattern) (ha : d85701 p = 1) (hb : d111645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85696 q = 1) (hb : d111640 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25231 q ha hb
    | true =>
      simp only [d85696, d111640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85697 q = 1) (hb : d111641 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d111641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85698 q = 1) (hb : d111642 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d111642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85699 q = 1) (hb : d111643 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d111643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85700 q = 1) (hb : d111644 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d111644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85701 q = 1) (hb : d111645 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d111645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25233 (p : Pattern) (ha : d85707 p = 1) (hb : d111651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85702 q = 1) (hb : d111646 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25232 q ha hb
    | true =>
      simp only [d85702, d111646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85703 q = 1) (hb : d111647 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d111647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85704 q = 1) (hb : d111648 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d111648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85705 q = 1) (hb : d111649 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d111649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85706 q = 1) (hb : d111650 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d111650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85707 q = 1) (hb : d111651 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d111651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25234 (p : Pattern) (ha : d85713 p = 1) (hb : d111657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85708 q = 1) (hb : d111652 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25233 q ha hb
    | true =>
      simp only [d85708, d111652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85709 q = 1) (hb : d111653 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d111653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85710 q = 1) (hb : d111654 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d111654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85711 q = 1) (hb : d111655 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d111655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85712 q = 1) (hb : d111656 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d111656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85713 q = 1) (hb : d111657 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d111657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25235 (p : Pattern) (ha : d85719 p = 1) (hb : d111663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85714 q = 1) (hb : d111658 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25234 q ha hb
    | true =>
      simp only [d85714, d111658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85715 q = 1) (hb : d111659 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d111659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85716 q = 1) (hb : d111660 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d111660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85717 q = 1) (hb : d111661 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d111661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85718 q = 1) (hb : d111662 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d111662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85719 q = 1) (hb : d111663 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d111663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro25236 (p : Pattern) (ha : d10654 p = 1) (hb : d85723 p = 1) : d88140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10652 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34 q = 1) (hb : d85721 q = 1) : d34 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10653 q = 1) (hb : d85723 q = 1) : d88139 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d85723, d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10653, d85723, d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10654 q = 1) (hb : d85723 q = 1) : d88140 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10654, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25237 (p : Pattern) (ha : d10660 p = 1) (hb : d85724 p = 1) : d88146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d85724 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10660 q = 1) (hb : d85724 q = 1) : d88146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25238 (p : Pattern) (ha : d85724 p = 1) (hb : d108784 p = 1) : d88152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25237 q ha hb
    | true =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108780 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108780, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108781 q = 1) : d88149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108781, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108782 q = 1) : d88150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108782, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108783 q = 1) : d88151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108783, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108784 q = 1) : d88152 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108784, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108784, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro25239 (p : Pattern) (ha : d10667 p = 1) (hb : d85724 p = 1) : d88153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10657 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d85724 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10667 q = 1) (hb : d85724 q = 1) : d88153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10667, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25240 (p : Pattern) (ha : d85724 p = 1) (hb : d108789 p = 1) : d88159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10274 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10275 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25237 q ha hb
    | true =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108780 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108780, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d108780, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108781 q = 1) : d88149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108781, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108781, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108782 q = 1) : d88150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108782, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d108782, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108783 q = 1) : d88151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108783, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d108783, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10279 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10280 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10668 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25239 q ha hb
    | true =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h23 (q : Pattern) (ha : d85724 q = 1) (hb : d108785 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d108785, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d85724 q = 1) (hb : d108786 q = 1) : d88156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d108786, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d85724 q = 1) (hb : d108787 q = 1) : d88157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108787, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d108787, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d85724 q = 1) (hb : d108788 q = 1) : d88158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108788, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d108788, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d85724 q = 1) (hb : d108789 q = 1) : d88159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108789, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d108789, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro25241 (p : Pattern) (ha : d85724 p = 1) (hb : d108796 p = 1) : d88164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10668 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25239 q ha hb
    | true =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108785 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108785, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108785, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108786 q = 1) : d88156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108786, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108786, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108794 q = 1) : d88157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108794, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108794, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108795 q = 1) : d88158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108795, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108795, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108796 q = 1) : d88164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108796, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108796, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25242 (p : Pattern) (ha : d10691 p = 1) (hb : d85723 p = 1) : d88171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d10689 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75 q = 1) (hb : d85721 q = 1) : d75 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10690 q = 1) (hb : d85723 q = 1) : d88170 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d85723, d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10690, d85723, d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10691 q = 1) (hb : d85723 q = 1) : d88171 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10691, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro25243 (p : Pattern) (ha : d10697 p = 1) (hb : d85724 p = 1) : d88177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d85723 q = 1) : d88172 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25242 q ha hb
    | true =>
      simp only [d10692, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d85723 q = 1) : d88173 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d79 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10694 q = 1) (hb : d85724 q = 1) : d88174 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d85724, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d85724, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10695 q = 1) (hb : d85724 q = 1) : d88175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10695, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10696 q = 1) (hb : d85724 q = 1) : d88176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10696, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d10697 q = 1) (hb : d85724 q = 1) : d88177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10697, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro25244 (p : Pattern) (ha : d85724 p = 1) (hb : d108806 p = 1) : d88183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10698 q = 1) (hb : d85724 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25243 q ha hb
    | true =>
      simp only [d10698, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
  have h2 (q : Pattern) (ha : d85724 q = 1) (hb : d108802 q = 1) : d88179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d108802, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d108802, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10268 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85724 q = 1) (hb : d108803 q = 1) : d88180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108803, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d108803, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108804 q = 1) : d88181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d108804, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108804, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85724 q = 1) (hb : d108805 q = 1) : d88182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d108805, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108805, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108806 q = 1) : d88183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108806, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108806, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro25245 (p : Pattern) (ha : d85724 p = 1) (hb : d108812 p = 1) : d88189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10271 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10271 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10272 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85724 q = 1) (hb : d108790 q = 1) : d88160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108790, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25238 q ha hb
    | true =>
      simp only [d108790, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25240 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10273 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d85724 q = 1) (hb : d108791 q = 1) : d88161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108791, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d108791, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d85724 q = 1) (hb : d108792 q = 1) : d88162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108792, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d108792, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d85724 q = 1) (hb : d108793 q = 1) : d88163 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108793, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d108793, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85724 q = 1) (hb : d108797 q = 1) : d88165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108797, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108797, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25241 q ha hb
  have h12 (q : Pattern) (ha : d85724 q = 1) (hb : d108798 q = 1) : d88166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108798, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d108798, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d85724 q = 1) (hb : d108799 q = 1) : d88167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108799, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d108799, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d85724 q = 1) (hb : d108800 q = 1) : d88168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108800, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d108800, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d85724 q = 1) (hb : d108801 q = 1) : d88169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108801, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d108801, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85724 q = 1) (hb : d108807 q = 1) : d88184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108807, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108807, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25244 q ha hb
  have h17 (q : Pattern) (ha : d85724 q = 1) (hb : d108808 q = 1) : d88185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108808, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d108808, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d85724 q = 1) (hb : d108809 q = 1) : d88186 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108809, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d108809, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d85724 q = 1) (hb : d108810 q = 1) : d88187 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108810, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d108810, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d85724 q = 1) (hb : d108811 q = 1) : d88188 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d108811, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d108811, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d85724 q = 1) (hb : d108812 q = 1) : d88189 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d108812, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d108812, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro25246 (p : Pattern) (ha : d10719 p = 1) (hb : d85724 p = 1) : d88199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25237 q ha hb
    | true =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d85724 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d85724 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d85724 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d85724 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10719 q = 1) (hb : d85724 q = 1) : d88199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro25247 (p : Pattern) (ha : d10726 p = 1) (hb : d85724 p = 1) : d88206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25237 q ha hb
    | true =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d85724 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d85724 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d85724 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d85724 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10668 q = 1) (hb : d85724 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25239 q ha hb
    | true =>
      simp only [d10668, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10264 q ha hb
  have h7 (q : Pattern) (ha : d10722 q = 1) (hb : d85724 q = 1) : d88202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10723 q = 1) (hb : d85724 q = 1) : d88203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10723, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10724 q = 1) (hb : d85724 q = 1) : d88204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10725 q = 1) (hb : d85724 q = 1) : d88205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10726 q = 1) (hb : d85724 q = 1) : d88206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10726, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25248 (p : Pattern) (ha : d10801 p = 1) (hb : d85724 p = 1) : d88253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d85724 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25237 q ha hb
    | true =>
      simp only [d10661, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d85724 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d85724 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d85724 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d85724 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10262 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10801 q = 1) (hb : d85724 q = 1) : d88253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10801, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro25249 (p : Pattern) (ha : d10731 p = 1) (hb : d85724 p = 1) : d88211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85724 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85723 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10655 q = 1) (hb : d85723 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25236 q ha hb
    | true =>
      simp only [d10655, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10656 q = 1) (hb : d85723 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10656, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d85724 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10657, d85724, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d85724 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d85724 q = 1) : d88210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10731 q = 1) (hb : d85724 q = 1) : d88211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
