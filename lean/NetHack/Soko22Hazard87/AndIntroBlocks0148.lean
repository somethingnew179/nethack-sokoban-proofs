import NetHack.Soko22Hazard87.AndIntroBlocks0147
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro37000 (p : Pattern) (ha : d15159 p = 1) (hb : d169395 p = 1) : d170277 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15155 q = 1) (hb : d169395 q = 1) : d170276 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15155, d169395, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15155, d169395, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15156 q = 1) (hb : d116750 q = 1) : d13353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15157 q = 1) (hb : d116750 q = 1) : d13354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15158 q = 1) (hb : d169395 q = 1) : d22238 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d169395, d22238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15158, d169395, d22238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15159 q = 1) (hb : d169395 q = 1) : d170277 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15159, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15159, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro37001 (p : Pattern) (ha : d15166 p = 1) (hb : d169395 p = 1) : d22249 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5138 q = 1) (hb : d169395 q = 1) : d22248 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5138, d169395, d22248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5138, d169395, d22248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15165 q = 1) (hb : d169395 q = 1) : d15165 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15166 q = 1) (hb : d169395 q = 1) : d22249 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15166, d22249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15166, d22249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37002 (p : Pattern) (ha : d15171 p = 1) (hb : d169395 p = 1) : d22255 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1588 q = 1) (hb : d169395 q = 1) : d22254 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d169395, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d169395, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15165 q = 1) (hb : d169395 q = 1) : d15165 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15171 q = 1) (hb : d169395 q = 1) : d22255 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15171, d22255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15171, d22255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37003 (p : Pattern) (ha : d15177 p = 1) (hb : d169395 p = 1) : d170290 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36998 q ha hb
    | true =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
    | true =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37001 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15172 q = 1) (hb : d169395 q = 1) : d170285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
    | true =>
      simp only [d15172, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37002 q ha hb
  have h9 (q : Pattern) (ha : d15173 q = 1) (hb : d169395 q = 1) : d170286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15174 q = 1) (hb : d169395 q = 1) : d170287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15175 q = 1) (hb : d169395 q = 1) : d170288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15175, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15176 q = 1) (hb : d169395 q = 1) : d170289 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15176, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15176, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15177 q = 1) (hb : d169395 q = 1) : d170290 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15177, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15177, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37004 (p : Pattern) (ha : d15181 p = 1) (hb : d169395 p = 1) : d170294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15172 q = 1) (hb : d169395 q = 1) : d170285 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15172, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
    | true =>
      simp only [d15172, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37002 q ha hb
  have h2 (q : Pattern) (ha : d15173 q = 1) (hb : d169395 q = 1) : d170286 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15173, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15173, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15174 q = 1) (hb : d169395 q = 1) : d170287 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15174, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15174, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15175 q = 1) (hb : d169395 q = 1) : d170288 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15175, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15175, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15180 q = 1) (hb : d169395 q = 1) : d170293 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15180, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15180, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15181 q = 1) (hb : d169395 q = 1) : d170294 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15181, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15181, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37005 (p : Pattern) (ha : d15187 p = 1) (hb : d169395 p = 1) : d170300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37003 q ha hb
    | true =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d169395 q = 1) : d170299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15187 q = 1) (hb : d169395 q = 1) : d170300 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15187, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15187, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37006 (p : Pattern) (ha : d15191 p = 1) (hb : d169395 p = 1) : d170304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d169395 q = 1) : d170303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15191 q = 1) (hb : d169395 q = 1) : d170304 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15191, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15191, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37007 (p : Pattern) (ha : d15197 p = 1) (hb : d169395 p = 1) : d170310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d169395 q = 1) : d170305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37005 q ha hb
    | true =>
      simp only [d15192, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37006 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d169395 q = 1) : d170306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d169395 q = 1) : d170307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d169395 q = 1) : d170308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d169395 q = 1) : d170309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15197 q = 1) (hb : d169395 q = 1) : d170310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15197, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15197, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37008 (p : Pattern) (ha : d15200 p = 1) (hb : d169395 p = 1) : d170313 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37003 q ha hb
    | true =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15186 q = 1) (hb : d169395 q = 1) : d170299 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15186, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15186, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15200 q = 1) (hb : d169395 q = 1) : d170313 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15200, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15200, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37009 (p : Pattern) (ha : d15201 p = 1) (hb : d169395 p = 1) : d170314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15190 q = 1) (hb : d169395 q = 1) : d170303 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15190, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15190, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15201 q = 1) (hb : d169395 q = 1) : d170314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15201, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15201, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37010 (p : Pattern) (ha : d15207 p = 1) (hb : d169395 p = 1) : d170320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15192 q = 1) (hb : d169395 q = 1) : d170305 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15192, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37005 q ha hb
    | true =>
      simp only [d15192, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37006 q ha hb
  have h2 (q : Pattern) (ha : d15193 q = 1) (hb : d169395 q = 1) : d170306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15193, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15193, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15194 q = 1) (hb : d169395 q = 1) : d170307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15194, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15194, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15195 q = 1) (hb : d169395 q = 1) : d170308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15195, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15195, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15196 q = 1) (hb : d169395 q = 1) : d170309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15196, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15196, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15202 q = 1) (hb : d169395 q = 1) : d170315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37008 q ha hb
    | true =>
      simp only [d15202, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37009 q ha hb
  have h7 (q : Pattern) (ha : d15203 q = 1) (hb : d169395 q = 1) : d170316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15204 q = 1) (hb : d169395 q = 1) : d170317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15204, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15205 q = 1) (hb : d169395 q = 1) : d170318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15206 q = 1) (hb : d169395 q = 1) : d170319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15207 q = 1) (hb : d169395 q = 1) : d170320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15207, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15207, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37011 (p : Pattern) (ha : d15248 p = 1) (hb : d169395 p = 1) : d170358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36998 q ha hb
    | true =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
    | true =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37001 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15246 q = 1) (hb : d169395 q = 1) : d170356 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15246, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15246, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15247 q = 1) (hb : d169395 q = 1) : d170357 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15247, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15247, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15248 q = 1) (hb : d169395 q = 1) : d170358 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15248, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15248, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro37012 (p : Pattern) (ha : d15258 p = 1) (hb : d169395 p = 1) : d170368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37011 q ha hb
    | true =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d169395 q = 1) : d170365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d169395 q = 1) : d170366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d169395 q = 1) : d170367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15258 q = 1) (hb : d169395 q = 1) : d170368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15258, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15258, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37013 (p : Pattern) (ha : d15358 p = 1) (hb : d169395 p = 1) : d170422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15348 q = 1) (hb : d169395 q = 1) : d170412 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15348, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37012 q ha hb
    | true =>
      simp only [d15348, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37006 q ha hb
  have h2 (q : Pattern) (ha : d15349 q = 1) (hb : d169395 q = 1) : d170413 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15349, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15349, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15350 q = 1) (hb : d169395 q = 1) : d170414 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15350, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15350, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15351 q = 1) (hb : d169395 q = 1) : d170415 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15351, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15351, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15352 q = 1) (hb : d169395 q = 1) : d170416 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15352, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15352, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15353 q = 1) (hb : d169395 q = 1) : d170417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37006 q ha hb
    | true =>
      simp only [d15353, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15354 q = 1) (hb : d169395 q = 1) : d170418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15355 q = 1) (hb : d169395 q = 1) : d170419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15355, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15356 q = 1) (hb : d169395 q = 1) : d170420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15357 q = 1) (hb : d169395 q = 1) : d170421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15358 q = 1) (hb : d169395 q = 1) : d170422 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15358, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15358, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37014 (p : Pattern) (ha : d15364 p = 1) (hb : d169395 p = 1) : d170428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15353 q = 1) (hb : d169395 q = 1) : d170417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15353, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37006 q ha hb
    | true =>
      simp only [d15353, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15354 q = 1) (hb : d169395 q = 1) : d170418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15354, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15354, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15355 q = 1) (hb : d169395 q = 1) : d170419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15355, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15355, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15356 q = 1) (hb : d169395 q = 1) : d170420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15356, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15356, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15357 q = 1) (hb : d169395 q = 1) : d170421 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15357, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15357, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15359 q = 1) (hb : d169395 q = 1) : d170423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37009 q ha hb
    | true =>
      simp only [d15359, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15360 q = 1) (hb : d169395 q = 1) : d170424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15361 q = 1) (hb : d169395 q = 1) : d170425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15361, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15362 q = 1) (hb : d169395 q = 1) : d170426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15363 q = 1) (hb : d169395 q = 1) : d170427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15364 q = 1) (hb : d169395 q = 1) : d170428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15364, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15364, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37015 (p : Pattern) (ha : d15373 p = 1) (hb : d169395 p = 1) : d170437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15359 q = 1) (hb : d169395 q = 1) : d170423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15359, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37009 q ha hb
    | true =>
      simp only [d15359, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15360 q = 1) (hb : d169395 q = 1) : d170424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15360, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15360, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15361 q = 1) (hb : d169395 q = 1) : d170425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15361, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15361, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15362 q = 1) (hb : d169395 q = 1) : d170426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15362, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15362, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15363 q = 1) (hb : d169395 q = 1) : d170427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15363, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15363, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15373 q = 1) (hb : d169395 q = 1) : d170437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15373, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15373, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37016 (p : Pattern) (ha : d15408 p = 1) (hb : d169395 p = 1) : d170458 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15407 q = 1) (hb : d169395 q = 1) : d170457 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15407, d169395, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15407, d169395, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15397 q = 1) (hb : d116750 q = 1) : d13490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
  have h10 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15398 q = 1) (hb : d116750 q = 1) : d13491 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15398, d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15399 q = 1) (hb : d116750 q = 1) : d13492 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15399, d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15400 q = 1) (hb : d116750 q = 1) : d13493 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15400, d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15401 q = 1) (hb : d169395 q = 1) : d22523 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d169395, d22523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15401, d169395, d22523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d15408 q = 1) (hb : d169395 q = 1) : d170458 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15408, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15408, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37017 (p : Pattern) (ha : d15435 p = 1) (hb : d169395 p = 1) : d22562 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1877 q = 1) (hb : d169395 q = 1) : d22561 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d169395, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d169395, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15416 q = 1) (hb : d169395 q = 1) : d15416 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15435 q = 1) (hb : d169395 q = 1) : d22562 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15435, d22562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15435, d22562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37018 (p : Pattern) (ha : d15441 p = 1) (hb : d169395 p = 1) : d170484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15436 q = 1) (hb : d169395 q = 1) : d170479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
    | true =>
      simp only [d15436, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37017 q ha hb
  have h2 (q : Pattern) (ha : d15437 q = 1) (hb : d169395 q = 1) : d170480 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15438 q = 1) (hb : d169395 q = 1) : d170481 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15439 q = 1) (hb : d169395 q = 1) : d170482 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15439, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15440 q = 1) (hb : d169395 q = 1) : d170483 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15440, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15440, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15441 q = 1) (hb : d169395 q = 1) : d170484 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15441, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15441, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37019 (p : Pattern) (ha : d15521 p = 1) (hb : d169395 p = 1) : d170515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15442 q = 1) (hb : d169395 q = 1) : d170485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37018 q ha hb
    | true =>
      simp only [d15442, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15443 q = 1) (hb : d169395 q = 1) : d170486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15518 q = 1) (hb : d169395 q = 1) : d170512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15518, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15518, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15519 q = 1) (hb : d169395 q = 1) : d170513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15519, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15519, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15520 q = 1) (hb : d169395 q = 1) : d170514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15520, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15520, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15521 q = 1) (hb : d169395 q = 1) : d170515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15521, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15521, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37020 (p : Pattern) (ha : d15527 p = 1) (hb : d169395 p = 1) : d170521 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15522 q = 1) (hb : d169395 q = 1) : d170516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15522, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37019 q ha hb
    | true =>
      simp only [d15522, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15523 q = 1) (hb : d169395 q = 1) : d170517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15523, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15523, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15524 q = 1) (hb : d169395 q = 1) : d170518 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15524, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15524, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15525 q = 1) (hb : d169395 q = 1) : d170519 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15525, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15525, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15526 q = 1) (hb : d169395 q = 1) : d170520 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15526, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15526, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15527 q = 1) (hb : d169395 q = 1) : d170521 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15527, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15527, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37021 (p : Pattern) (ha : d15212 p = 1) (hb : d169395 p = 1) : d170325 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37003 q ha hb
    | true =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d169395 q = 1) : d170324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15212 q = 1) (hb : d169395 q = 1) : d170325 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15212, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15212, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37022 (p : Pattern) (ha : d15214 p = 1) (hb : d169395 p = 1) : d170327 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d169395 q = 1) : d170326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15214 q = 1) (hb : d169395 q = 1) : d170327 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15214, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15214, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37023 (p : Pattern) (ha : d15221 p = 1) (hb : d169395 p = 1) : d170334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37003 q ha hb
    | true =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d169395 q = 1) : d170332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d169395 q = 1) : d170333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15221 q = 1) (hb : d169395 q = 1) : d170334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15221, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15221, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37024 (p : Pattern) (ha : d15224 p = 1) (hb : d169395 p = 1) : d170337 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d169395 q = 1) : d170335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d169395 q = 1) : d170336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15224 q = 1) (hb : d169395 q = 1) : d170337 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15224, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15224, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37025 (p : Pattern) (ha : d15232 p = 1) (hb : d169395 p = 1) : d170342 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15228 q = 1) (hb : d169395 q = 1) : d170341 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15228, d169395, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15228, d169395, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15231 q = 1) (hb : d169395 q = 1) : d15231 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15232 q = 1) (hb : d169395 q = 1) : d170342 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15232, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15232, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37026 (p : Pattern) (ha : d15237 p = 1) (hb : d169395 p = 1) : d170347 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15236 q = 1) (hb : d169395 q = 1) : d170346 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15236, d169395, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15236, d169395, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15156 q = 1) (hb : d116750 q = 1) : d13353 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15156, d13353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15157 q = 1) (hb : d116750 q = 1) : d13354 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15157, d13354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15158 q = 1) (hb : d169395 q = 1) : d22238 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15158, d169395, d22238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15158, d169395, d22238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15237 q = 1) (hb : d169395 q = 1) : d170347 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15237, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15237, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro37027 (p : Pattern) (ha : d15243 p = 1) (hb : d169395 p = 1) : d170353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15233 q = 1) (hb : d169395 q = 1) : d170343 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15233, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37025 q ha hb
    | true =>
      simp only [d15233, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36998 q ha hb
  have h2 (q : Pattern) (ha : d15234 q = 1) (hb : d169395 q = 1) : d170344 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15234, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15234, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15235 q = 1) (hb : d169395 q = 1) : d170345 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15235, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15235, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15238 q = 1) (hb : d169395 q = 1) : d170348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15238, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36998 q ha hb
    | true =>
      simp only [d15238, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37026 q ha hb
  have h5 (q : Pattern) (ha : d15239 q = 1) (hb : d169395 q = 1) : d170349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15239, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15239, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15240 q = 1) (hb : d169395 q = 1) : d170350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15240, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15240, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15241 q = 1) (hb : d169395 q = 1) : d170351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15241, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15241, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15160 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36998 q ha hb
    | true =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
  have h9 (q : Pattern) (ha : d15161 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15162 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15167 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
    | true =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37001 q ha hb
  have h12 (q : Pattern) (ha : d15168 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15169 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15170 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15242 q = 1) (hb : d169395 q = 1) : d170352 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15242, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15242, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15243 q = 1) (hb : d169395 q = 1) : d170353 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15243, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15243, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro37028 (p : Pattern) (ha : d15254 p = 1) (hb : d169395 p = 1) : d170364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d169395 q = 1) : d170354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37027 q ha hb
    | true =>
      simp only [d15244, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d169395 q = 1) : d170355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37011 q ha hb
    | true =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d169395 q = 1) : d170361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d169395 q = 1) : d170362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d169395 q = 1) : d170363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15254 q = 1) (hb : d169395 q = 1) : d170364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15254, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15254, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37029 (p : Pattern) (ha : d13287 p = 1) (hb : d169395 p = 1) : d22421 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1588 q = 1) (hb : d169395 q = 1) : d22254 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1588, d169395, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1588, d169395, d22254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13287 q = 1) (hb : d169395 q = 1) : d22421 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13287, d22421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13287, d22421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37030 (p : Pattern) (ha : d15309 p = 1) (hb : d169395 p = 1) : d170376 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15160 q = 1) (hb : d169395 q = 1) : d170278 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36998 q ha hb
    | true =>
      simp only [d15160, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
  have h2 (q : Pattern) (ha : d15161 q = 1) (hb : d169395 q = 1) : d170279 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15161, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15162 q = 1) (hb : d169395 q = 1) : d170280 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15162, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15167 q = 1) (hb : d169395 q = 1) : d170281 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
    | true =>
      simp only [d15167, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37001 q ha hb
  have h5 (q : Pattern) (ha : d15168 q = 1) (hb : d169395 q = 1) : d170282 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15168, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15169 q = 1) (hb : d169395 q = 1) : d170283 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15169, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15170 q = 1) (hb : d169395 q = 1) : d170284 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15170, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15304 q = 1) (hb : d169395 q = 1) : d170371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15304, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37000 q ha hb
    | true =>
      simp only [d15304, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37029 q ha hb
  have h9 (q : Pattern) (ha : d15305 q = 1) (hb : d169395 q = 1) : d170372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15305, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15305, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15306 q = 1) (hb : d169395 q = 1) : d170373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15306, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15306, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15307 q = 1) (hb : d169395 q = 1) : d170374 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15307, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15307, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15308 q = 1) (hb : d169395 q = 1) : d170375 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15308, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15308, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15309 q = 1) (hb : d169395 q = 1) : d170376 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15309, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15309, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37031 (p : Pattern) (ha : d15315 p = 1) (hb : d169395 p = 1) : d170382 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d169395 q = 1) : d170377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37030 q ha hb
    | true =>
      simp only [d15310, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d169395 q = 1) : d170378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d169395 q = 1) : d170379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d169395 q = 1) : d170380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d169395 q = 1) : d170381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15315 q = 1) (hb : d169395 q = 1) : d170382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15315, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15315, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37032 (p : Pattern) (ha : d125617 p = 1) (hb : d169395 p = 1) : d170388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d169395 q = 1) : d170328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37021 q ha hb
    | true =>
      simp only [d15215, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37022 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d169395 q = 1) : d170329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d169395 q = 1) : d170330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d169395 q = 1) : d170331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d169395 q = 1) : d170338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37023 q ha hb
    | true =>
      simp only [d15225, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37024 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d169395 q = 1) : d170339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d169395 q = 1) : d170340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d169395 q = 1) : d170369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37028 q ha hb
    | true =>
      simp only [d15259, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37012 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d169395 q = 1) : d170370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d169395 q = 1) : d170383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37031 q ha hb
    | true =>
      simp only [d15316, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d169395 q = 1) : d170384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d169395 q = 1) : d170385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d169395 q = 1) : d170386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d169395 q = 1) : d170387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125617 q = 1) (hb : d169395 q = 1) : d170388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125617, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125617, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37033 (p : Pattern) (ha : d15322 p = 1) (hb : d169395 p = 1) : d170389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37003 q ha hb
    | true =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15185 q = 1) (hb : d169395 q = 1) : d170298 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15185, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15211 q = 1) (hb : d169395 q = 1) : d170324 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15211, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15211, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15322 q = 1) (hb : d169395 q = 1) : d170389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15322, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15322, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37034 (p : Pattern) (ha : d15323 p = 1) (hb : d169395 p = 1) : d170390 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15189 q = 1) (hb : d169395 q = 1) : d170302 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15189, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15213 q = 1) (hb : d169395 q = 1) : d170326 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15213, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15213, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15323 q = 1) (hb : d169395 q = 1) : d170390 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15323, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15323, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37035 (p : Pattern) (ha : d15328 p = 1) (hb : d169395 p = 1) : d170395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15178 q = 1) (hb : d169395 q = 1) : d170291 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37003 q ha hb
    | true =>
      simp only [d15178, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15179 q = 1) (hb : d169395 q = 1) : d170292 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15179, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15184 q = 1) (hb : d169395 q = 1) : d170297 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15184, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15219 q = 1) (hb : d169395 q = 1) : d170332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15219, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15219, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15220 q = 1) (hb : d169395 q = 1) : d170333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15220, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15220, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15328 q = 1) (hb : d169395 q = 1) : d170395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15328, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15328, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37036 (p : Pattern) (ha : d15329 p = 1) (hb : d169395 p = 1) : d170396 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15188 q = 1) (hb : d169395 q = 1) : d170301 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15188, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15222 q = 1) (hb : d169395 q = 1) : d170335 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15222, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15222, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15223 q = 1) (hb : d169395 q = 1) : d170336 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15223, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15223, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15329 q = 1) (hb : d169395 q = 1) : d170396 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15329, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15329, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37037 (p : Pattern) (ha : d15333 p = 1) (hb : d169395 p = 1) : d170400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15244 q = 1) (hb : d169395 q = 1) : d170354 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15244, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37027 q ha hb
    | true =>
      simp only [d15244, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15245 q = 1) (hb : d169395 q = 1) : d170355 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15245, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15245, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15249 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37011 q ha hb
    | true =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15250 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15251 q = 1) (hb : d169395 q = 1) : d170361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15251, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15251, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15252 q = 1) (hb : d169395 q = 1) : d170362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15252, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15252, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15253 q = 1) (hb : d169395 q = 1) : d170363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15253, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15253, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15333 q = 1) (hb : d169395 q = 1) : d170400 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15333, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15333, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37038 (p : Pattern) (ha : d15334 p = 1) (hb : d169395 p = 1) : d170401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15249 q = 1) (hb : d169395 q = 1) : d170359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37011 q ha hb
    | true =>
      simp only [d15249, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15250 q = 1) (hb : d169395 q = 1) : d170360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15250, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15182 q = 1) (hb : d169395 q = 1) : d170295 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37004 q ha hb
    | true =>
      simp only [d15182, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15183 q = 1) (hb : d169395 q = 1) : d170296 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15183, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15255 q = 1) (hb : d169395 q = 1) : d170365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15255, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15255, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15256 q = 1) (hb : d169395 q = 1) : d170366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15256, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15256, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15257 q = 1) (hb : d169395 q = 1) : d170367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15257, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15257, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15334 q = 1) (hb : d169395 q = 1) : d170401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15334, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15334, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37039 (p : Pattern) (ha : d15340 p = 1) (hb : d169395 p = 1) : d170404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15310 q = 1) (hb : d169395 q = 1) : d170377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15310, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37030 q ha hb
    | true =>
      simp only [d15310, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15311 q = 1) (hb : d169395 q = 1) : d170378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15311, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15311, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15312 q = 1) (hb : d169395 q = 1) : d170379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15312, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15312, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15313 q = 1) (hb : d169395 q = 1) : d170380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15313, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15313, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15314 q = 1) (hb : d169395 q = 1) : d170381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15314, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15314, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15340 q = 1) (hb : d169395 q = 1) : d170404 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15340, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15340, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37040 (p : Pattern) (ha : d125622 p = 1) (hb : d169395 p = 1) : d170410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15215 q = 1) (hb : d169395 q = 1) : d170328 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15215, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37021 q ha hb
    | true =>
      simp only [d15215, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37022 q ha hb
  have h2 (q : Pattern) (ha : d15216 q = 1) (hb : d169395 q = 1) : d170329 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15216, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15216, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15217 q = 1) (hb : d169395 q = 1) : d170330 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15217, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15217, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15218 q = 1) (hb : d169395 q = 1) : d170331 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15218, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15218, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15225 q = 1) (hb : d169395 q = 1) : d170338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15225, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37023 q ha hb
    | true =>
      simp only [d15225, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37024 q ha hb
  have h6 (q : Pattern) (ha : d15226 q = 1) (hb : d169395 q = 1) : d170339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15226, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15226, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15227 q = 1) (hb : d169395 q = 1) : d170340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15227, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15227, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15259 q = 1) (hb : d169395 q = 1) : d170369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15259, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37028 q ha hb
    | true =>
      simp only [d15259, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37012 q ha hb
  have h9 (q : Pattern) (ha : d125613 q = 1) (hb : d169395 q = 1) : d170370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125613, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125613, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15316 q = 1) (hb : d169395 q = 1) : d170383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15316, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37031 q ha hb
    | true =>
      simp only [d15316, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15317 q = 1) (hb : d169395 q = 1) : d170384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15317, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15317, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125614 q = 1) (hb : d169395 q = 1) : d170385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125614, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125614, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125615 q = 1) (hb : d169395 q = 1) : d170386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125615, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125615, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125616 q = 1) (hb : d169395 q = 1) : d170387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125616, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125616, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15324 q = 1) (hb : d169395 q = 1) : d170391 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15324, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37033 q ha hb
    | true =>
      simp only [d15324, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37034 q ha hb
  have h16 (q : Pattern) (ha : d15325 q = 1) (hb : d169395 q = 1) : d170392 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15325, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15325, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15326 q = 1) (hb : d169395 q = 1) : d170393 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15326, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15326, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15327 q = 1) (hb : d169395 q = 1) : d170394 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15327, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15327, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15330 q = 1) (hb : d169395 q = 1) : d170397 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15330, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37035 q ha hb
    | true =>
      simp only [d15330, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37036 q ha hb
  have h20 (q : Pattern) (ha : d15331 q = 1) (hb : d169395 q = 1) : d170398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15331, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15331, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15332 q = 1) (hb : d169395 q = 1) : d170399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15332, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15332, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15335 q = 1) (hb : d169395 q = 1) : d170402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37037 q ha hb
    | true =>
      simp only [d15335, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37038 q ha hb
  have h23 (q : Pattern) (ha : d125618 q = 1) (hb : d169395 q = 1) : d170403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125618, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15341 q = 1) (hb : d169395 q = 1) : d170405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37039 q ha hb
    | true =>
      simp only [d15341, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15342 q = 1) (hb : d169395 q = 1) : d170406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15342, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125619 q = 1) (hb : d169395 q = 1) : d170407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125619, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125620 q = 1) (hb : d169395 q = 1) : d170408 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125620, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125620, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125621 q = 1) (hb : d169395 q = 1) : d170409 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125621, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125621, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125622 q = 1) (hb : d169395 q = 1) : d170410 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125622, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125622, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro37041 (p : Pattern) (ha : d125629 p = 1) (hb : d169395 p = 1) : d170435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15335 q = 1) (hb : d169395 q = 1) : d170402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15335, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37037 q ha hb
    | true =>
      simp only [d15335, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37038 q ha hb
  have h2 (q : Pattern) (ha : d125618 q = 1) (hb : d169395 q = 1) : d170403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125618, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125618, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15341 q = 1) (hb : d169395 q = 1) : d170405 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15341, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37039 q ha hb
    | true =>
      simp only [d15341, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15342 q = 1) (hb : d169395 q = 1) : d170406 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15342, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15342, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125619 q = 1) (hb : d169395 q = 1) : d170407 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125619, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125619, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125627 q = 1) (hb : d169395 q = 1) : d170433 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125627, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125627, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125628 q = 1) (hb : d169395 q = 1) : d170434 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125628, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125628, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125629 q = 1) (hb : d169395 q = 1) : d170435 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125629, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125629, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37042 (p : Pattern) (ha : d15385 p = 1) (hb : d169395 p = 1) : d170444 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15379 q = 1) (hb : d169395 q = 1) : d170443 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15379, d169395, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15379, d169395, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15384 q = 1) (hb : d169395 q = 1) : d15384 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15385 q = 1) (hb : d169395 q = 1) : d170444 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15385, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15385, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37043 (p : Pattern) (ha : d15392 p = 1) (hb : d169395 p = 1) : d170447 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15386 q = 1) (hb : d169395 q = 1) : d170445 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15386, d169395, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15386, d169395, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15387 q = 1) (hb : d116750 q = 1) : d22502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d22502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36997 q ha hb
  have h10 (q : Pattern) (ha : d10063 q = 1) (hb : d116750 q = 1) : d22226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36997 q ha hb
    | true =>
      simp only [d10063, d22226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15388 q = 1) (hb : d116750 q = 1) : d22503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15388, d22503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10065 q = 1) (hb : d116750 q = 1) : d22227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10065, d22227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15389 q = 1) (hb : d116750 q = 1) : d22504 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15389, d22504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15390 q = 1) (hb : d116750 q = 1) : d22505 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15390, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15390, d22505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15391 q = 1) (hb : d169395 q = 1) : d170446 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15391, d169395, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15391, d169395, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d15392 q = 1) (hb : d169395 q = 1) : d170447 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15392, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15392, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37044 (p : Pattern) (ha : d15402 p = 1) (hb : d169395 p = 1) : d170452 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15396 q = 1) (hb : d169395 q = 1) : d170451 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15396, d169395, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15396, d169395, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15397 q = 1) (hb : d116750 q = 1) : d13490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d13490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
  have h10 (q : Pattern) (ha : d10085 q = 1) (hb : d116750 q = 1) : d13351 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36999 q ha hb
    | true =>
      simp only [d10085, d13351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15398 q = 1) (hb : d116750 q = 1) : d13491 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15398, d13491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10087 q = 1) (hb : d116750 q = 1) : d13352 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10087, d13352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15399 q = 1) (hb : d116750 q = 1) : d13492 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15399, d13492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15400 q = 1) (hb : d116750 q = 1) : d13493 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15400, d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15400, d13493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15401 q = 1) (hb : d169395 q = 1) : d22523 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15401, d169395, d22523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15401, d169395, d22523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d15402 q = 1) (hb : d169395 q = 1) : d170452 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15402, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15402, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37045 (p : Pattern) (ha : d15417 p = 1) (hb : d169395 p = 1) : d22543 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6500 q = 1) (hb : d169395 q = 1) : d22542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6500, d169395, d22542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6500, d169395, d22542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15416 q = 1) (hb : d169395 q = 1) : d15416 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15417 q = 1) (hb : d169395 q = 1) : d22543 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15417, d22543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15417, d22543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37046 (p : Pattern) (ha : d15423 p = 1) (hb : d169395 p = 1) : d170467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15393 q = 1) (hb : d169395 q = 1) : d170448 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15393, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37042 q ha hb
    | true =>
      simp only [d15393, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37043 q ha hb
  have h2 (q : Pattern) (ha : d15394 q = 1) (hb : d169395 q = 1) : d170449 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15394, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15394, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15395 q = 1) (hb : d169395 q = 1) : d170450 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15395, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15395, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15403 q = 1) (hb : d169395 q = 1) : d170453 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15403, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37043 q ha hb
    | true =>
      simp only [d15403, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37044 q ha hb
  have h5 (q : Pattern) (ha : d15404 q = 1) (hb : d169395 q = 1) : d170454 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15404, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15404, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15405 q = 1) (hb : d169395 q = 1) : d170455 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15405, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15405, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15406 q = 1) (hb : d169395 q = 1) : d170456 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15406, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15406, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15409 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37043 q ha hb
    | true =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
  have h9 (q : Pattern) (ha : d15410 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15411 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15418 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
    | true =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37045 q ha hb
  have h12 (q : Pattern) (ha : d15419 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15420 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15421 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15422 q = 1) (hb : d169395 q = 1) : d170466 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15422, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15422, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15423 q = 1) (hb : d169395 q = 1) : d170467 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15423, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15423, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro37047 (p : Pattern) (ha : d15428 p = 1) (hb : d169395 p = 1) : d170472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37043 q ha hb
    | true =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
    | true =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37045 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15426 q = 1) (hb : d169395 q = 1) : d170470 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15426, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15426, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15427 q = 1) (hb : d169395 q = 1) : d170471 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15427, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15427, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15428 q = 1) (hb : d169395 q = 1) : d170472 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15428, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15428, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro37048 (p : Pattern) (ha : d15434 p = 1) (hb : d169395 p = 1) : d170478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15424 q = 1) (hb : d169395 q = 1) : d170468 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15424, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37046 q ha hb
    | true =>
      simp only [d15424, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15425 q = 1) (hb : d169395 q = 1) : d170469 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15425, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15425, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15429 q = 1) (hb : d169395 q = 1) : d170473 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37047 q ha hb
    | true =>
      simp only [d15429, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15430 q = 1) (hb : d169395 q = 1) : d170474 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15431 q = 1) (hb : d169395 q = 1) : d170475 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15431, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15431, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15432 q = 1) (hb : d169395 q = 1) : d170476 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15432, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15432, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15433 q = 1) (hb : d169395 q = 1) : d170477 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15433, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15433, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15434 q = 1) (hb : d169395 q = 1) : d170478 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15434, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15434, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37049 (p : Pattern) (ha : d15447 p = 1) (hb : d169395 p = 1) : d170490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15429 q = 1) (hb : d169395 q = 1) : d170473 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15429, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37047 q ha hb
    | true =>
      simp only [d15429, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15430 q = 1) (hb : d169395 q = 1) : d170474 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15430, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15430, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d169395 q = 1) : d170485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37018 q ha hb
    | true =>
      simp only [d15442, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d169395 q = 1) : d170486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15444 q = 1) (hb : d169395 q = 1) : d170487 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15444, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15444, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15445 q = 1) (hb : d169395 q = 1) : d170488 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15445, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15445, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15446 q = 1) (hb : d169395 q = 1) : d170489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15446, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15446, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15447 q = 1) (hb : d169395 q = 1) : d170490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15447, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15447, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37050 (p : Pattern) (ha : d13516 p = 1) (hb : d169395 p = 1) : d22639 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1877 q = 1) (hb : d169395 q = 1) : d22561 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d169395, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1877, d169395, d22561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13516 q = 1) (hb : d169395 q = 1) : d22639 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13516, d22639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13516, d22639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37051 (p : Pattern) (ha : d15504 p = 1) (hb : d169395 p = 1) : d170498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37043 q ha hb
    | true =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
    | true =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37045 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15499 q = 1) (hb : d169395 q = 1) : d170493 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15499, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
    | true =>
      simp only [d15499, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37050 q ha hb
  have h9 (q : Pattern) (ha : d15500 q = 1) (hb : d169395 q = 1) : d170494 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15500, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15500, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15501 q = 1) (hb : d169395 q = 1) : d170495 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15501, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15501, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15502 q = 1) (hb : d169395 q = 1) : d170496 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15502, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15502, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15503 q = 1) (hb : d169395 q = 1) : d170497 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15503, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15503, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15504 q = 1) (hb : d169395 q = 1) : d170498 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15504, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15504, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37052 (p : Pattern) (ha : d15510 p = 1) (hb : d169395 p = 1) : d170504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15505 q = 1) (hb : d169395 q = 1) : d170499 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15505, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37051 q ha hb
    | true =>
      simp only [d15505, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15506 q = 1) (hb : d169395 q = 1) : d170500 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15506, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15506, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15507 q = 1) (hb : d169395 q = 1) : d170501 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15507, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15507, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15508 q = 1) (hb : d169395 q = 1) : d170502 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15508, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15508, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15509 q = 1) (hb : d169395 q = 1) : d170503 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15509, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15509, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15510 q = 1) (hb : d169395 q = 1) : d170504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15510, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15510, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37053 (p : Pattern) (ha : d125639 p = 1) (hb : d169395 p = 1) : d170510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15448 q = 1) (hb : d169395 q = 1) : d170491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15448, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37048 q ha hb
    | true =>
      simp only [d15448, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37049 q ha hb
  have h2 (q : Pattern) (ha : d125635 q = 1) (hb : d169395 q = 1) : d170492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125635, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125635, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15511 q = 1) (hb : d169395 q = 1) : d170505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15511, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37052 q ha hb
    | true =>
      simp only [d15511, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15512 q = 1) (hb : d169395 q = 1) : d170506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15512, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15512, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125636 q = 1) (hb : d169395 q = 1) : d170507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125636, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125636, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125637 q = 1) (hb : d169395 q = 1) : d170508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125637, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125637, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125638 q = 1) (hb : d169395 q = 1) : d170509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125638, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125638, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125639 q = 1) (hb : d169395 q = 1) : d170510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125639, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125639, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37054 (p : Pattern) (ha : d125645 p = 1) (hb : d169395 p = 1) : d170527 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15198 q = 1) (hb : d169395 q = 1) : d170311 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15198, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15198, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37007 q ha hb
  have h2 (q : Pattern) (ha : d15199 q = 1) (hb : d169395 q = 1) : d170312 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15199, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15199, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15208 q = 1) (hb : d169395 q = 1) : d170321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37007 q ha hb
    | true =>
      simp only [d15208, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37010 q ha hb
  have h4 (q : Pattern) (ha : d15209 q = 1) (hb : d169395 q = 1) : d170322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15209, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15210 q = 1) (hb : d169395 q = 1) : d170323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15210, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15210, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125623 q = 1) (hb : d169395 q = 1) : d170411 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125623, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37032 q ha hb
    | true =>
      simp only [d125623, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37040 q ha hb
  have h7 (q : Pattern) (ha : d15365 q = 1) (hb : d169395 q = 1) : d170429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15365, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37013 q ha hb
    | true =>
      simp only [d15365, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37014 q ha hb
  have h8 (q : Pattern) (ha : d125624 q = 1) (hb : d169395 q = 1) : d170430 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125624, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125624, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125625 q = 1) (hb : d169395 q = 1) : d170431 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125625, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125625, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125626 q = 1) (hb : d169395 q = 1) : d170432 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125626, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125626, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125630 q = 1) (hb : d169395 q = 1) : d170436 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125630, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125630, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37041 q ha hb
  have h12 (q : Pattern) (ha : d15374 q = 1) (hb : d169395 q = 1) : d170438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15374, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15374, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37015 q ha hb
  have h13 (q : Pattern) (ha : d125631 q = 1) (hb : d169395 q = 1) : d170439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125631, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125631, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125632 q = 1) (hb : d169395 q = 1) : d170440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125632, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125632, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125633 q = 1) (hb : d169395 q = 1) : d170441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125633, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125633, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125634 q = 1) (hb : d169395 q = 1) : d170442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125634, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125634, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125640 q = 1) (hb : d169395 q = 1) : d170511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125640, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125640, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37053 q ha hb
  have h18 (q : Pattern) (ha : d15528 q = 1) (hb : d169395 q = 1) : d170522 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15528, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15528, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37020 q ha hb
  have h19 (q : Pattern) (ha : d125641 q = 1) (hb : d169395 q = 1) : d170523 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125641, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125641, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125642 q = 1) (hb : d169395 q = 1) : d170524 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125642, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125642, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125643 q = 1) (hb : d169395 q = 1) : d170525 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125643, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125643, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125644 q = 1) (hb : d169395 q = 1) : d170526 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125644, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125644, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125645 q = 1) (hb : d169395 q = 1) : d170527 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125645, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125645, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37055 (p : Pattern) (ha : d125651 p = 1) (hb : d169395 p = 1) : d170533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125646 q = 1) (hb : d169395 q = 1) : d170528 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125646, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125646, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37054 q ha hb
  have h2 (q : Pattern) (ha : d125647 q = 1) (hb : d169395 q = 1) : d170529 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125647, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125647, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125648 q = 1) (hb : d169395 q = 1) : d170530 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125648, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125648, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125649 q = 1) (hb : d169395 q = 1) : d170531 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125649, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125649, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125650 q = 1) (hb : d169395 q = 1) : d170532 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125650, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125650, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125651 q = 1) (hb : d169395 q = 1) : d170533 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125651, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125651, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37056 (p : Pattern) (ha : d15546 p = 1) (hb : d169395 p = 1) : d170539 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15544 q = 1) (hb : d169395 q = 1) : d170538 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15544, d169395, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15544, d169395, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15545 q = 1) (hb : d169395 q = 1) : d15545 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15546 q = 1) (hb : d169395 q = 1) : d170539 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15546, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15546, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37057 (p : Pattern) (ha : d10370 p = 1) (hb : d116750 p = 1) : d13677 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d5717 q = 1) : d5717 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5245 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10370 q = 1) (hb : d116750 q = 1) : d13677 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10370, d116750, d13677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d10370, d116750, d13677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h2 p ha hb
theorem andIntro37058 (p : Pattern) (ha : d15551 p = 1) (hb : d169395 p = 1) : d170541 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15547 q = 1) (hb : d169395 q = 1) : d170540 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15547, d169395, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15547, d169395, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10371 q = 1) (hb : d116750 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10373 q = 1) (hb : d116750 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15548 q = 1) (hb : d116750 q = 1) : d13680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15549 q = 1) (hb : d116750 q = 1) : d13681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15550 q = 1) (hb : d169395 q = 1) : d22693 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d169395, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15550, d169395, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h12 (q : Pattern) (ha : d15551 q = 1) (hb : d169395 q = 1) : d170541 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15551, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15551, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro37059 (p : Pattern) (ha : d15558 p = 1) (hb : d169395 p = 1) : d22704 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5251 q = 1) (hb : d169395 q = 1) : d22703 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5251, d169395, d22703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5251, d169395, d22703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15557 q = 1) (hb : d169395 q = 1) : d15557 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15558 q = 1) (hb : d169395 q = 1) : d22704 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15558, d22704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15558, d22704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37060 (p : Pattern) (ha : d15563 p = 1) (hb : d169395 p = 1) : d22710 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2071 q = 1) (hb : d169395 q = 1) : d22709 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d169395, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d169395, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15557 q = 1) (hb : d169395 q = 1) : d15557 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15563 q = 1) (hb : d169395 q = 1) : d22710 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15563, d22710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15563, d22710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37061 (p : Pattern) (ha : d15569 p = 1) (hb : d169395 p = 1) : d170554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37056 q ha hb
    | true =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
    | true =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37059 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15564 q = 1) (hb : d169395 q = 1) : d170549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
    | true =>
      simp only [d15564, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37060 q ha hb
  have h9 (q : Pattern) (ha : d15565 q = 1) (hb : d169395 q = 1) : d170550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15566 q = 1) (hb : d169395 q = 1) : d170551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15567 q = 1) (hb : d169395 q = 1) : d170552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15567, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15568 q = 1) (hb : d169395 q = 1) : d170553 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15568, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15568, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15569 q = 1) (hb : d169395 q = 1) : d170554 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15569, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15569, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37062 (p : Pattern) (ha : d15573 p = 1) (hb : d169395 p = 1) : d170558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15564 q = 1) (hb : d169395 q = 1) : d170549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15564, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
    | true =>
      simp only [d15564, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37060 q ha hb
  have h2 (q : Pattern) (ha : d15565 q = 1) (hb : d169395 q = 1) : d170550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15565, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15565, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15566 q = 1) (hb : d169395 q = 1) : d170551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15566, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15566, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15567 q = 1) (hb : d169395 q = 1) : d170552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15567, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15567, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15572 q = 1) (hb : d169395 q = 1) : d170557 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15572, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15572, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15573 q = 1) (hb : d169395 q = 1) : d170558 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15573, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15573, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37063 (p : Pattern) (ha : d15579 p = 1) (hb : d169395 p = 1) : d170564 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37061 q ha hb
    | true =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d169395 q = 1) : d170563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15579 q = 1) (hb : d169395 q = 1) : d170564 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15579, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15579, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37064 (p : Pattern) (ha : d15583 p = 1) (hb : d169395 p = 1) : d170568 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d169395 q = 1) : d170567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15583 q = 1) (hb : d169395 q = 1) : d170568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15583, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15583, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37065 (p : Pattern) (ha : d15589 p = 1) (hb : d169395 p = 1) : d170574 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d169395 q = 1) : d170569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37063 q ha hb
    | true =>
      simp only [d15584, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37064 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d169395 q = 1) : d170570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d169395 q = 1) : d170571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d169395 q = 1) : d170572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d169395 q = 1) : d170573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15589 q = 1) (hb : d169395 q = 1) : d170574 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15589, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15589, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37066 (p : Pattern) (ha : d15592 p = 1) (hb : d169395 p = 1) : d170577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37061 q ha hb
    | true =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15578 q = 1) (hb : d169395 q = 1) : d170563 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15578, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15578, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15592 q = 1) (hb : d169395 q = 1) : d170577 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15592, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15592, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37067 (p : Pattern) (ha : d15593 p = 1) (hb : d169395 p = 1) : d170578 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15582 q = 1) (hb : d169395 q = 1) : d170567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15582, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15582, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15593 q = 1) (hb : d169395 q = 1) : d170578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15593, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15593, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37068 (p : Pattern) (ha : d15599 p = 1) (hb : d169395 p = 1) : d170584 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15584 q = 1) (hb : d169395 q = 1) : d170569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15584, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37063 q ha hb
    | true =>
      simp only [d15584, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37064 q ha hb
  have h2 (q : Pattern) (ha : d15585 q = 1) (hb : d169395 q = 1) : d170570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15585, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15585, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15586 q = 1) (hb : d169395 q = 1) : d170571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15586, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15586, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15587 q = 1) (hb : d169395 q = 1) : d170572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15587, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15587, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15588 q = 1) (hb : d169395 q = 1) : d170573 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15588, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15588, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15594 q = 1) (hb : d169395 q = 1) : d170579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37066 q ha hb
    | true =>
      simp only [d15594, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37067 q ha hb
  have h7 (q : Pattern) (ha : d15595 q = 1) (hb : d169395 q = 1) : d170580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15596 q = 1) (hb : d169395 q = 1) : d170581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15596, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15597 q = 1) (hb : d169395 q = 1) : d170582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15598 q = 1) (hb : d169395 q = 1) : d170583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15599 q = 1) (hb : d169395 q = 1) : d170584 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15599, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15599, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37069 (p : Pattern) (ha : d15636 p = 1) (hb : d169395 p = 1) : d170619 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37056 q ha hb
    | true =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
    | true =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37059 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15634 q = 1) (hb : d169395 q = 1) : d170617 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15634, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15634, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15635 q = 1) (hb : d169395 q = 1) : d170618 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15635, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15635, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15636 q = 1) (hb : d169395 q = 1) : d170619 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15636, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15636, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro37070 (p : Pattern) (ha : d15646 p = 1) (hb : d169395 p = 1) : d170629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37069 q ha hb
    | true =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d169395 q = 1) : d170626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d169395 q = 1) : d170627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d169395 q = 1) : d170628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15646 q = 1) (hb : d169395 q = 1) : d170629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15646, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15646, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37071 (p : Pattern) (ha : d15746 p = 1) (hb : d169395 p = 1) : d170683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15736 q = 1) (hb : d169395 q = 1) : d170673 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15736, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37070 q ha hb
    | true =>
      simp only [d15736, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37064 q ha hb
  have h2 (q : Pattern) (ha : d15737 q = 1) (hb : d169395 q = 1) : d170674 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15737, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15737, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15738 q = 1) (hb : d169395 q = 1) : d170675 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15738, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15738, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15739 q = 1) (hb : d169395 q = 1) : d170676 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15739, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15739, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15740 q = 1) (hb : d169395 q = 1) : d170677 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15740, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15740, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15741 q = 1) (hb : d169395 q = 1) : d170678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37064 q ha hb
    | true =>
      simp only [d15741, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15742 q = 1) (hb : d169395 q = 1) : d170679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15743 q = 1) (hb : d169395 q = 1) : d170680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15743, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15744 q = 1) (hb : d169395 q = 1) : d170681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15745 q = 1) (hb : d169395 q = 1) : d170682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15746 q = 1) (hb : d169395 q = 1) : d170683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15746, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15746, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37072 (p : Pattern) (ha : d15752 p = 1) (hb : d169395 p = 1) : d170689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15741 q = 1) (hb : d169395 q = 1) : d170678 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15741, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37064 q ha hb
    | true =>
      simp only [d15741, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15742 q = 1) (hb : d169395 q = 1) : d170679 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15742, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15742, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15743 q = 1) (hb : d169395 q = 1) : d170680 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15743, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15743, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15744 q = 1) (hb : d169395 q = 1) : d170681 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15744, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15744, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15745 q = 1) (hb : d169395 q = 1) : d170682 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15745, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15745, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15747 q = 1) (hb : d169395 q = 1) : d170684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37067 q ha hb
    | true =>
      simp only [d15747, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15748 q = 1) (hb : d169395 q = 1) : d170685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15749 q = 1) (hb : d169395 q = 1) : d170686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15749, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15750 q = 1) (hb : d169395 q = 1) : d170687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15751 q = 1) (hb : d169395 q = 1) : d170688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15752 q = 1) (hb : d169395 q = 1) : d170689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15752, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15752, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37073 (p : Pattern) (ha : d15761 p = 1) (hb : d169395 p = 1) : d170698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15747 q = 1) (hb : d169395 q = 1) : d170684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15747, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37067 q ha hb
    | true =>
      simp only [d15747, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15748 q = 1) (hb : d169395 q = 1) : d170685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15748, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15748, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15749 q = 1) (hb : d169395 q = 1) : d170686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15749, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15749, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15750 q = 1) (hb : d169395 q = 1) : d170687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15750, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15750, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15751 q = 1) (hb : d169395 q = 1) : d170688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15751, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15751, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15761 q = 1) (hb : d169395 q = 1) : d170698 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15761, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15761, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37074 (p : Pattern) (ha : d15786 p = 1) (hb : d169395 p = 1) : d170715 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15785 q = 1) (hb : d169395 q = 1) : d170714 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15785, d169395, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15785, d169395, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15775 q = 1) (hb : d116750 q = 1) : d13817 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
  have h10 (q : Pattern) (ha : d10371 q = 1) (hb : d116750 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15776 q = 1) (hb : d116750 q = 1) : d13818 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10373 q = 1) (hb : d116750 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15777 q = 1) (hb : d116750 q = 1) : d13819 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15778 q = 1) (hb : d116750 q = 1) : d13820 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d15779 q = 1) (hb : d169395 q = 1) : d22937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d169395, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15779, d169395, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d15786 q = 1) (hb : d169395 q = 1) : d170715 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15786, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15786, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37075 (p : Pattern) (ha : d15813 p = 1) (hb : d169395 p = 1) : d22976 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2355 q = 1) (hb : d169395 q = 1) : d22975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d169395, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d169395, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15794 q = 1) (hb : d169395 q = 1) : d15794 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15813 q = 1) (hb : d169395 q = 1) : d22976 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15813, d22976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15813, d22976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37076 (p : Pattern) (ha : d15819 p = 1) (hb : d169395 p = 1) : d170741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15814 q = 1) (hb : d169395 q = 1) : d170736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
    | true =>
      simp only [d15814, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37075 q ha hb
  have h2 (q : Pattern) (ha : d15815 q = 1) (hb : d169395 q = 1) : d170737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15816 q = 1) (hb : d169395 q = 1) : d170738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15817 q = 1) (hb : d169395 q = 1) : d170739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15817, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15818 q = 1) (hb : d169395 q = 1) : d170740 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15818, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15818, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15819 q = 1) (hb : d169395 q = 1) : d170741 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15819, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15819, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37077 (p : Pattern) (ha : d15899 p = 1) (hb : d169395 p = 1) : d170772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15820 q = 1) (hb : d169395 q = 1) : d170742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37076 q ha hb
    | true =>
      simp only [d15820, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15821 q = 1) (hb : d169395 q = 1) : d170743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15896 q = 1) (hb : d169395 q = 1) : d170769 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15896, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15896, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15897 q = 1) (hb : d169395 q = 1) : d170770 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15897, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15897, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15898 q = 1) (hb : d169395 q = 1) : d170771 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15898, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15898, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15899 q = 1) (hb : d169395 q = 1) : d170772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15899, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15899, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37078 (p : Pattern) (ha : d15905 p = 1) (hb : d169395 p = 1) : d170778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15900 q = 1) (hb : d169395 q = 1) : d170773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15900, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37077 q ha hb
    | true =>
      simp only [d15900, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15901 q = 1) (hb : d169395 q = 1) : d170774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15901, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15901, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15902 q = 1) (hb : d169395 q = 1) : d170775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15902, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15902, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15903 q = 1) (hb : d169395 q = 1) : d170776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15903, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15903, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15904 q = 1) (hb : d169395 q = 1) : d170777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15904, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15904, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15905 q = 1) (hb : d169395 q = 1) : d170778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d15905, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15905, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37079 (p : Pattern) (ha : d15604 p = 1) (hb : d169395 p = 1) : d170589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37061 q ha hb
    | true =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d169395 q = 1) : d170588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15604 q = 1) (hb : d169395 q = 1) : d170589 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15604, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15604, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37080 (p : Pattern) (ha : d15606 p = 1) (hb : d169395 p = 1) : d170591 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d169395 q = 1) : d170590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15606 q = 1) (hb : d169395 q = 1) : d170591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15606, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15606, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37081 (p : Pattern) (ha : d15613 p = 1) (hb : d169395 p = 1) : d170598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37061 q ha hb
    | true =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d169395 q = 1) : d170596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d169395 q = 1) : d170597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15613 q = 1) (hb : d169395 q = 1) : d170598 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15613, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15613, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37082 (p : Pattern) (ha : d15616 p = 1) (hb : d169395 p = 1) : d170601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d169395 q = 1) : d170599 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d169395 q = 1) : d170600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15616 q = 1) (hb : d169395 q = 1) : d170601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15616, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15616, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37083 (p : Pattern) (ha : d15621 p = 1) (hb : d169395 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15620 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15620, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15620, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15621 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37084 (p : Pattern) (ha : d15625 p = 1) (hb : d169395 p = 1) : d170608 p = 1 := by
  have h0 (q : Pattern) (ha : d15545 q = 1) (hb : d169395 q = 1) : d15545 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10371 q = 1) (hb : d116750 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10373 q = 1) (hb : d116750 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15548 q = 1) (hb : d116750 q = 1) : d13680 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15548, d13680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15549 q = 1) (hb : d116750 q = 1) : d13681 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15549, d13681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d15550 q = 1) (hb : d169395 q = 1) : d22693 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15550, d169395, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15550, d169395, d22693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15625 q = 1) (hb : d169395 q = 1) : d170608 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15625, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15625, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37085 (p : Pattern) (ha : d15631 p = 1) (hb : d169395 p = 1) : d170614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15622 q = 1) (hb : d169395 q = 1) : d170605 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15622, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37083 q ha hb
    | true =>
      simp only [d15622, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37056 q ha hb
  have h2 (q : Pattern) (ha : d15623 q = 1) (hb : d169395 q = 1) : d170606 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15623, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15623, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15624 q = 1) (hb : d169395 q = 1) : d170607 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15624, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15624, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15626 q = 1) (hb : d169395 q = 1) : d170609 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15626, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37056 q ha hb
    | true =>
      simp only [d15626, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37084 q ha hb
  have h5 (q : Pattern) (ha : d15627 q = 1) (hb : d169395 q = 1) : d170610 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15627, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15627, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15628 q = 1) (hb : d169395 q = 1) : d170611 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15628, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15628, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15629 q = 1) (hb : d169395 q = 1) : d170612 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15629, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15629, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15552 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37056 q ha hb
    | true =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
  have h9 (q : Pattern) (ha : d15553 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15554 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15559 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
    | true =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37059 q ha hb
  have h12 (q : Pattern) (ha : d15560 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15561 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15562 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15630 q = 1) (hb : d169395 q = 1) : d170613 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15630, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15630, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15631 q = 1) (hb : d169395 q = 1) : d170614 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15631, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15631, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro37086 (p : Pattern) (ha : d15642 p = 1) (hb : d169395 p = 1) : d170625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d169395 q = 1) : d170615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37085 q ha hb
    | true =>
      simp only [d15632, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d169395 q = 1) : d170616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37069 q ha hb
    | true =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d169395 q = 1) : d170622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d169395 q = 1) : d170623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d169395 q = 1) : d170624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15642 q = 1) (hb : d169395 q = 1) : d170625 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15642, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15642, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37087 (p : Pattern) (ha : d13614 p = 1) (hb : d169395 p = 1) : d22854 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d2071 q = 1) (hb : d169395 q = 1) : d22709 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d169395, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2071, d169395, d22709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d13614 q = 1) (hb : d169395 q = 1) : d22854 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13614, d22854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13614, d22854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37088 (p : Pattern) (ha : d15697 p = 1) (hb : d169395 p = 1) : d170637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15552 q = 1) (hb : d169395 q = 1) : d170542 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37056 q ha hb
    | true =>
      simp only [d15552, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
  have h2 (q : Pattern) (ha : d15553 q = 1) (hb : d169395 q = 1) : d170543 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15553, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15554 q = 1) (hb : d169395 q = 1) : d170544 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15554, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15559 q = 1) (hb : d169395 q = 1) : d170545 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
    | true =>
      simp only [d15559, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37059 q ha hb
  have h5 (q : Pattern) (ha : d15560 q = 1) (hb : d169395 q = 1) : d170546 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15560, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15561 q = 1) (hb : d169395 q = 1) : d170547 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15561, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15562 q = 1) (hb : d169395 q = 1) : d170548 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15562, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15692 q = 1) (hb : d169395 q = 1) : d170632 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15692, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37058 q ha hb
    | true =>
      simp only [d15692, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37087 q ha hb
  have h9 (q : Pattern) (ha : d15693 q = 1) (hb : d169395 q = 1) : d170633 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15693, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15693, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15694 q = 1) (hb : d169395 q = 1) : d170634 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15694, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15694, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15695 q = 1) (hb : d169395 q = 1) : d170635 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15695, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15695, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15696 q = 1) (hb : d169395 q = 1) : d170636 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15696, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15696, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15697 q = 1) (hb : d169395 q = 1) : d170637 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15697, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15697, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37089 (p : Pattern) (ha : d15703 p = 1) (hb : d169395 p = 1) : d170643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d169395 q = 1) : d170638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37088 q ha hb
    | true =>
      simp only [d15698, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d169395 q = 1) : d170639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d169395 q = 1) : d170640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d169395 q = 1) : d170641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d169395 q = 1) : d170642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15703 q = 1) (hb : d169395 q = 1) : d170643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15703, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15703, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37090 (p : Pattern) (ha : d125660 p = 1) (hb : d169395 p = 1) : d170649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d169395 q = 1) : d170592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37079 q ha hb
    | true =>
      simp only [d15607, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37080 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d169395 q = 1) : d170593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d169395 q = 1) : d170594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d169395 q = 1) : d170595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d169395 q = 1) : d170602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37081 q ha hb
    | true =>
      simp only [d15617, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37082 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d169395 q = 1) : d170603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d169395 q = 1) : d170604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d169395 q = 1) : d170630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37086 q ha hb
    | true =>
      simp only [d15647, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37070 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d169395 q = 1) : d170631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d169395 q = 1) : d170644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37089 q ha hb
    | true =>
      simp only [d15704, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d169395 q = 1) : d170645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d169395 q = 1) : d170646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d169395 q = 1) : d170647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d169395 q = 1) : d170648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125660 q = 1) (hb : d169395 q = 1) : d170649 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125660, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125660, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37091 (p : Pattern) (ha : d15710 p = 1) (hb : d169395 p = 1) : d170650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37061 q ha hb
    | true =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15577 q = 1) (hb : d169395 q = 1) : d170562 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15577, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15603 q = 1) (hb : d169395 q = 1) : d170588 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15603, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15603, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15710 q = 1) (hb : d169395 q = 1) : d170650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15710, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15710, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37092 (p : Pattern) (ha : d15711 p = 1) (hb : d169395 p = 1) : d170651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15581 q = 1) (hb : d169395 q = 1) : d170566 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15581, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15605 q = 1) (hb : d169395 q = 1) : d170590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15605, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15605, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15711 q = 1) (hb : d169395 q = 1) : d170651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15711, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15711, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37093 (p : Pattern) (ha : d15716 p = 1) (hb : d169395 p = 1) : d170656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15570 q = 1) (hb : d169395 q = 1) : d170555 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37061 q ha hb
    | true =>
      simp only [d15570, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15571 q = 1) (hb : d169395 q = 1) : d170556 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15571, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15576 q = 1) (hb : d169395 q = 1) : d170561 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15576, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15611 q = 1) (hb : d169395 q = 1) : d170596 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15611, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15611, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15612 q = 1) (hb : d169395 q = 1) : d170597 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15612, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15612, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15716 q = 1) (hb : d169395 q = 1) : d170656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15716, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15716, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37094 (p : Pattern) (ha : d15717 p = 1) (hb : d169395 p = 1) : d170657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15580 q = 1) (hb : d169395 q = 1) : d170565 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15580, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15614 q = 1) (hb : d169395 q = 1) : d170599 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15614, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15614, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15615 q = 1) (hb : d169395 q = 1) : d170600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15615, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15615, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15717 q = 1) (hb : d169395 q = 1) : d170657 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15717, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15717, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37095 (p : Pattern) (ha : d15721 p = 1) (hb : d169395 p = 1) : d170661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15632 q = 1) (hb : d169395 q = 1) : d170615 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15632, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37085 q ha hb
    | true =>
      simp only [d15632, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15633 q = 1) (hb : d169395 q = 1) : d170616 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15633, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15633, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15637 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37069 q ha hb
    | true =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15638 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15639 q = 1) (hb : d169395 q = 1) : d170622 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15639, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15639, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15640 q = 1) (hb : d169395 q = 1) : d170623 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15640, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15640, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15641 q = 1) (hb : d169395 q = 1) : d170624 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15641, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15641, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15721 q = 1) (hb : d169395 q = 1) : d170661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15721, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15721, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37096 (p : Pattern) (ha : d15722 p = 1) (hb : d169395 p = 1) : d170662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15637 q = 1) (hb : d169395 q = 1) : d170620 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37069 q ha hb
    | true =>
      simp only [d15637, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15638 q = 1) (hb : d169395 q = 1) : d170621 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15638, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15574 q = 1) (hb : d169395 q = 1) : d170559 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37062 q ha hb
    | true =>
      simp only [d15574, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15575 q = 1) (hb : d169395 q = 1) : d170560 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15575, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15643 q = 1) (hb : d169395 q = 1) : d170626 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15643, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15643, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15644 q = 1) (hb : d169395 q = 1) : d170627 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15644, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15644, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15645 q = 1) (hb : d169395 q = 1) : d170628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15645, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15645, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15722 q = 1) (hb : d169395 q = 1) : d170662 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15722, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15722, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37097 (p : Pattern) (ha : d15728 p = 1) (hb : d169395 p = 1) : d170665 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15698 q = 1) (hb : d169395 q = 1) : d170638 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15698, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37088 q ha hb
    | true =>
      simp only [d15698, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15699 q = 1) (hb : d169395 q = 1) : d170639 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15699, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15699, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15700 q = 1) (hb : d169395 q = 1) : d170640 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15700, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15700, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15701 q = 1) (hb : d169395 q = 1) : d170641 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15701, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15701, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15702 q = 1) (hb : d169395 q = 1) : d170642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15702, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15702, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15728 q = 1) (hb : d169395 q = 1) : d170665 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15728, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15728, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37098 (p : Pattern) (ha : d125665 p = 1) (hb : d169395 p = 1) : d170671 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15607 q = 1) (hb : d169395 q = 1) : d170592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15607, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37079 q ha hb
    | true =>
      simp only [d15607, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37080 q ha hb
  have h2 (q : Pattern) (ha : d15608 q = 1) (hb : d169395 q = 1) : d170593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15608, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15608, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15609 q = 1) (hb : d169395 q = 1) : d170594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15609, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15609, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15610 q = 1) (hb : d169395 q = 1) : d170595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15610, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15610, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15617 q = 1) (hb : d169395 q = 1) : d170602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15617, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37081 q ha hb
    | true =>
      simp only [d15617, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37082 q ha hb
  have h6 (q : Pattern) (ha : d15618 q = 1) (hb : d169395 q = 1) : d170603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15618, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15618, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15619 q = 1) (hb : d169395 q = 1) : d170604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15619, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15619, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15647 q = 1) (hb : d169395 q = 1) : d170630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15647, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37086 q ha hb
    | true =>
      simp only [d15647, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37070 q ha hb
  have h9 (q : Pattern) (ha : d125656 q = 1) (hb : d169395 q = 1) : d170631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125656, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125656, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15704 q = 1) (hb : d169395 q = 1) : d170644 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15704, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37089 q ha hb
    | true =>
      simp only [d15704, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15705 q = 1) (hb : d169395 q = 1) : d170645 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15705, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15705, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d125657 q = 1) (hb : d169395 q = 1) : d170646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125657, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d125657, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125658 q = 1) (hb : d169395 q = 1) : d170647 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125658, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d125658, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125659 q = 1) (hb : d169395 q = 1) : d170648 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125659, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125659, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15712 q = 1) (hb : d169395 q = 1) : d170652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15712, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37091 q ha hb
    | true =>
      simp only [d15712, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37092 q ha hb
  have h16 (q : Pattern) (ha : d15713 q = 1) (hb : d169395 q = 1) : d170653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15713, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15713, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d15714 q = 1) (hb : d169395 q = 1) : d170654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15714, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d15714, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d15715 q = 1) (hb : d169395 q = 1) : d170655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15715, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15715, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d15718 q = 1) (hb : d169395 q = 1) : d170658 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15718, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37093 q ha hb
    | true =>
      simp only [d15718, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37094 q ha hb
  have h20 (q : Pattern) (ha : d15719 q = 1) (hb : d169395 q = 1) : d170659 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15719, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15719, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d15720 q = 1) (hb : d169395 q = 1) : d170660 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15720, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d15720, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d15723 q = 1) (hb : d169395 q = 1) : d170663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37095 q ha hb
    | true =>
      simp only [d15723, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37096 q ha hb
  have h23 (q : Pattern) (ha : d125661 q = 1) (hb : d169395 q = 1) : d170664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d125661, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d15729 q = 1) (hb : d169395 q = 1) : d170666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37097 q ha hb
    | true =>
      simp only [d15729, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d15730 q = 1) (hb : d169395 q = 1) : d170667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d15730, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d125662 q = 1) (hb : d169395 q = 1) : d170668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d125662, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d125663 q = 1) (hb : d169395 q = 1) : d170669 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125663, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125663, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d125664 q = 1) (hb : d169395 q = 1) : d170670 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125664, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d125664, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d125665 q = 1) (hb : d169395 q = 1) : d170671 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125665, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125665, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro37099 (p : Pattern) (ha : d125672 p = 1) (hb : d169395 p = 1) : d170696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15723 q = 1) (hb : d169395 q = 1) : d170663 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15723, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37095 q ha hb
    | true =>
      simp only [d15723, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37096 q ha hb
  have h2 (q : Pattern) (ha : d125661 q = 1) (hb : d169395 q = 1) : d170664 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125661, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125661, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15729 q = 1) (hb : d169395 q = 1) : d170666 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15729, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37097 q ha hb
    | true =>
      simp only [d15729, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15730 q = 1) (hb : d169395 q = 1) : d170667 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15730, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15730, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125662 q = 1) (hb : d169395 q = 1) : d170668 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125662, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125662, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125670 q = 1) (hb : d169395 q = 1) : d170694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125670, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125670, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125671 q = 1) (hb : d169395 q = 1) : d170695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125671, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125671, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125672 q = 1) (hb : d169395 q = 1) : d170696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125672, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125672, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37100 (p : Pattern) (ha : d15768 p = 1) (hb : d169395 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15767 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15767, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15767, d169395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15768 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37101 (p : Pattern) (ha : d15771 p = 1) (hb : d169395 p = 1) : d170705 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15769 q = 1) (hb : d169395 q = 1) : d170704 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15769, d169395, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15769, d169395, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15770 q = 1) (hb : d169395 q = 1) : d15770 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15771 q = 1) (hb : d169395 q = 1) : d170705 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15771, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15771, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37102 (p : Pattern) (ha : d15780 p = 1) (hb : d169395 p = 1) : d170709 p = 1 := by
  have h0 (q : Pattern) (ha : d15770 q = 1) (hb : d169395 q = 1) : d15770 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d15775 q = 1) (hb : d116750 q = 1) : d13817 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15775, d13817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
  have h3 (q : Pattern) (ha : d10371 q = 1) (hb : d116750 q = 1) : d13678 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37057 q ha hb
    | true =>
      simp only [d10371, d13678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d15776 q = 1) (hb : d116750 q = 1) : d13818 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15776, d13818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10373 q = 1) (hb : d116750 q = 1) : d13679 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10373, d13679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d15777 q = 1) (hb : d116750 q = 1) : d13819 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15777, d13819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15778 q = 1) (hb : d116750 q = 1) : d13820 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15778, d13820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d15779 q = 1) (hb : d169395 q = 1) : d22937 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15779, d169395, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15779, d169395, d22937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15780 q = 1) (hb : d169395 q = 1) : d170709 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15780, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15780, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37103 (p : Pattern) (ha : d15795 p = 1) (hb : d169395 p = 1) : d22957 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d6647 q = 1) (hb : d169395 q = 1) : d22956 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d6647, d169395, d22956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d6647, d169395, d22956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15794 q = 1) (hb : d169395 q = 1) : d15794 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15795 q = 1) (hb : d169395 q = 1) : d22957 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15795, d22957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15795, d22957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37104 (p : Pattern) (ha : d15801 p = 1) (hb : d169395 p = 1) : d170724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15772 q = 1) (hb : d169395 q = 1) : d170706 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15772, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37100 q ha hb
    | true =>
      simp only [d15772, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37101 q ha hb
  have h2 (q : Pattern) (ha : d15773 q = 1) (hb : d169395 q = 1) : d170707 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15773, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15773, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15774 q = 1) (hb : d169395 q = 1) : d170708 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15774, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15774, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15781 q = 1) (hb : d169395 q = 1) : d170710 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15781, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37101 q ha hb
    | true =>
      simp only [d15781, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37102 q ha hb
  have h5 (q : Pattern) (ha : d15782 q = 1) (hb : d169395 q = 1) : d170711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15782, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15782, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15783 q = 1) (hb : d169395 q = 1) : d170712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15783, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15783, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15784 q = 1) (hb : d169395 q = 1) : d170713 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15784, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15784, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15787 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37101 q ha hb
    | true =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
  have h9 (q : Pattern) (ha : d15788 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15789 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15796 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
    | true =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37103 q ha hb
  have h12 (q : Pattern) (ha : d15797 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15798 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15799 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15800 q = 1) (hb : d169395 q = 1) : d170723 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15800, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15800, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15801 q = 1) (hb : d169395 q = 1) : d170724 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15801, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d15801, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro37105 (p : Pattern) (ha : d15806 p = 1) (hb : d169395 p = 1) : d170729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37101 q ha hb
    | true =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
    | true =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37103 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15804 q = 1) (hb : d169395 q = 1) : d170727 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15804, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15804, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15805 q = 1) (hb : d169395 q = 1) : d170728 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15805, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15805, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15806 q = 1) (hb : d169395 q = 1) : d170729 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15806, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15806, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro37106 (p : Pattern) (ha : d15812 p = 1) (hb : d169395 p = 1) : d170735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15802 q = 1) (hb : d169395 q = 1) : d170725 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15802, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37104 q ha hb
    | true =>
      simp only [d15802, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15803 q = 1) (hb : d169395 q = 1) : d170726 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15803, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15803, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15807 q = 1) (hb : d169395 q = 1) : d170730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37105 q ha hb
    | true =>
      simp only [d15807, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15808 q = 1) (hb : d169395 q = 1) : d170731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15809 q = 1) (hb : d169395 q = 1) : d170732 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15809, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15809, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15810 q = 1) (hb : d169395 q = 1) : d170733 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15810, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15810, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15811 q = 1) (hb : d169395 q = 1) : d170734 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15811, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15811, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15812 q = 1) (hb : d169395 q = 1) : d170735 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15812, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15812, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37107 (p : Pattern) (ha : d15825 p = 1) (hb : d169395 p = 1) : d170747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15807 q = 1) (hb : d169395 q = 1) : d170730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15807, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37105 q ha hb
    | true =>
      simp only [d15807, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15808 q = 1) (hb : d169395 q = 1) : d170731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15808, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15808, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d169395 q = 1) : d170742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37076 q ha hb
    | true =>
      simp only [d15820, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d169395 q = 1) : d170743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15822 q = 1) (hb : d169395 q = 1) : d170744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15822, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15822, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15823 q = 1) (hb : d169395 q = 1) : d170745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15823, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15823, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15824 q = 1) (hb : d169395 q = 1) : d170746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15824, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15824, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15825 q = 1) (hb : d169395 q = 1) : d170747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15825, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15825, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37108 (p : Pattern) (ha : d13843 p = 1) (hb : d169395 p = 1) : d23045 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2355 q = 1) (hb : d169395 q = 1) : d22975 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d169395, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2355, d169395, d22975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d13843 q = 1) (hb : d169395 q = 1) : d23045 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13843, d23045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13843, d23045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37109 (p : Pattern) (ha : d15882 p = 1) (hb : d169395 p = 1) : d170755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37101 q ha hb
    | true =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
    | true =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37103 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15877 q = 1) (hb : d169395 q = 1) : d170750 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15877, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
    | true =>
      simp only [d15877, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37108 q ha hb
  have h9 (q : Pattern) (ha : d15878 q = 1) (hb : d169395 q = 1) : d170751 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15878, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15878, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15879 q = 1) (hb : d169395 q = 1) : d170752 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15879, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15879, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15880 q = 1) (hb : d169395 q = 1) : d170753 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15880, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15880, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15881 q = 1) (hb : d169395 q = 1) : d170754 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15881, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15881, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15882 q = 1) (hb : d169395 q = 1) : d170755 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15882, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15882, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37110 (p : Pattern) (ha : d15888 p = 1) (hb : d169395 p = 1) : d170761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15883 q = 1) (hb : d169395 q = 1) : d170756 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15883, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37109 q ha hb
    | true =>
      simp only [d15883, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15884 q = 1) (hb : d169395 q = 1) : d170757 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15884, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15884, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15885 q = 1) (hb : d169395 q = 1) : d170758 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15885, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15885, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15886 q = 1) (hb : d169395 q = 1) : d170759 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15886, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15886, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15887 q = 1) (hb : d169395 q = 1) : d170760 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15887, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15887, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d15888 q = 1) (hb : d169395 q = 1) : d170761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15888, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15888, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37111 (p : Pattern) (ha : d125682 p = 1) (hb : d169395 p = 1) : d170767 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15826 q = 1) (hb : d169395 q = 1) : d170748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15826, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37106 q ha hb
    | true =>
      simp only [d15826, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37107 q ha hb
  have h2 (q : Pattern) (ha : d125678 q = 1) (hb : d169395 q = 1) : d170749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125678, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125678, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15889 q = 1) (hb : d169395 q = 1) : d170762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15889, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37110 q ha hb
    | true =>
      simp only [d15889, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15890 q = 1) (hb : d169395 q = 1) : d170763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15890, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15890, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125679 q = 1) (hb : d169395 q = 1) : d170764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d125679, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125679, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125680 q = 1) (hb : d169395 q = 1) : d170765 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d125680, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125680, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125681 q = 1) (hb : d169395 q = 1) : d170766 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d125681, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125681, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d125682 q = 1) (hb : d169395 q = 1) : d170767 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d125682, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125682, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37112 (p : Pattern) (ha : d125688 p = 1) (hb : d169395 p = 1) : d170784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15590 q = 1) (hb : d169395 q = 1) : d170575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15590, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15590, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37065 q ha hb
  have h2 (q : Pattern) (ha : d15591 q = 1) (hb : d169395 q = 1) : d170576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15591, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15591, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d15600 q = 1) (hb : d169395 q = 1) : d170585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37065 q ha hb
    | true =>
      simp only [d15600, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37068 q ha hb
  have h4 (q : Pattern) (ha : d15601 q = 1) (hb : d169395 q = 1) : d170586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15601, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d15602 q = 1) (hb : d169395 q = 1) : d170587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d15602, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15602, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125666 q = 1) (hb : d169395 q = 1) : d170672 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125666, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37090 q ha hb
    | true =>
      simp only [d125666, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37098 q ha hb
  have h7 (q : Pattern) (ha : d15753 q = 1) (hb : d169395 q = 1) : d170690 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15753, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37071 q ha hb
    | true =>
      simp only [d15753, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37072 q ha hb
  have h8 (q : Pattern) (ha : d125667 q = 1) (hb : d169395 q = 1) : d170691 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125667, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125667, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125668 q = 1) (hb : d169395 q = 1) : d170692 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125668, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d125668, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d125669 q = 1) (hb : d169395 q = 1) : d170693 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125669, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125669, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125673 q = 1) (hb : d169395 q = 1) : d170697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125673, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125673, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37099 q ha hb
  have h12 (q : Pattern) (ha : d15762 q = 1) (hb : d169395 q = 1) : d170699 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15762, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15762, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37073 q ha hb
  have h13 (q : Pattern) (ha : d125674 q = 1) (hb : d169395 q = 1) : d170700 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125674, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d125674, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125675 q = 1) (hb : d169395 q = 1) : d170701 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125675, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d125675, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d125676 q = 1) (hb : d169395 q = 1) : d170702 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125676, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d125676, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d125677 q = 1) (hb : d169395 q = 1) : d170703 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125677, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125677, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d125683 q = 1) (hb : d169395 q = 1) : d170768 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d125683, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125683, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37111 q ha hb
  have h18 (q : Pattern) (ha : d15906 q = 1) (hb : d169395 q = 1) : d170779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15906, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15906, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37078 q ha hb
  have h19 (q : Pattern) (ha : d125684 q = 1) (hb : d169395 q = 1) : d170780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d125684, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d125684, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d125685 q = 1) (hb : d169395 q = 1) : d170781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d125685, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d125685, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d125686 q = 1) (hb : d169395 q = 1) : d170782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d125686, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d125686, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d125687 q = 1) (hb : d169395 q = 1) : d170783 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d125687, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d125687, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d125688 q = 1) (hb : d169395 q = 1) : d170784 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d125688, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d125688, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37113 (p : Pattern) (ha : d125694 p = 1) (hb : d169395 p = 1) : d170790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125689 q = 1) (hb : d169395 q = 1) : d170785 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d125689, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125689, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37112 q ha hb
  have h2 (q : Pattern) (ha : d125690 q = 1) (hb : d169395 q = 1) : d170786 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d125690, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125690, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d125691 q = 1) (hb : d169395 q = 1) : d170787 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d125691, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125691, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125692 q = 1) (hb : d169395 q = 1) : d170788 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d125692, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125692, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d125693 q = 1) (hb : d169395 q = 1) : d170789 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d125693, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125693, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125694 q = 1) (hb : d169395 q = 1) : d170790 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d125694, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125694, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37114 (p : Pattern) (ha : d125700 p = 1) (hb : d169395 p = 1) : d170796 p = 1 := by
  have h0 (q : Pattern) (ha : d125529 q = 1) (hb : d169395 q = 1) : d169789 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125529, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36849 q ha hb
    | true =>
      simp only [d125529, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36891 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d125569 q = 1) (hb : d169395 q = 1) : d170005 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125569, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125569, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36936 q ha hb
  have h3 (q : Pattern) (ha : d125570 q = 1) (hb : d169395 q = 1) : d170006 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125570, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125570, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d125610 q = 1) (hb : d169395 q = 1) : d170270 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125610, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125610, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36996 q ha hb
  have h5 (q : Pattern) (ha : d125611 q = 1) (hb : d169395 q = 1) : d170271 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125611, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125611, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d125612 q = 1) (hb : d169395 q = 1) : d170272 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125612, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125612, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d125652 q = 1) (hb : d169395 q = 1) : d170534 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125652, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125652, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37055 q ha hb
  have h8 (q : Pattern) (ha : d125653 q = 1) (hb : d169395 q = 1) : d170535 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125653, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125653, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d125654 q = 1) (hb : d169395 q = 1) : d170536 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125654, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125654, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d125655 q = 1) (hb : d169395 q = 1) : d170537 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125655, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d125655, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d125695 q = 1) (hb : d169395 q = 1) : d170791 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d125695, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125695, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37113 q ha hb
  have h12 (q : Pattern) (ha : d125696 q = 1) (hb : d169395 q = 1) : d170792 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d125696, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125696, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d125697 q = 1) (hb : d169395 q = 1) : d170793 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d125697, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125697, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d125698 q = 1) (hb : d169395 q = 1) : d170794 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d125698, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125698, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d125699 q = 1) (hb : d169395 q = 1) : d170795 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d125699, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d125699, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d125700 q = 1) (hb : d169395 q = 1) : d170796 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d125700, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d125700, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro37115 (p : Pattern) (ha : d125706 p = 1) (hb : d169395 p = 1) : d170802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125701 q = 1) (hb : d169395 q = 1) : d170797 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d125701, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37114 q ha hb
    | true =>
      simp only [d125701, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125702 q = 1) (hb : d169395 q = 1) : d170798 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d125702, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125702, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125703 q = 1) (hb : d169395 q = 1) : d170799 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d125703, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125703, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125704 q = 1) (hb : d169395 q = 1) : d170800 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d125704, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125704, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125705 q = 1) (hb : d169395 q = 1) : d170801 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d125705, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125705, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125706 q = 1) (hb : d169395 q = 1) : d170802 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d125706, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125706, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37116 (p : Pattern) (ha : d125712 p = 1) (hb : d169395 p = 1) : d170808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125707 q = 1) (hb : d169395 q = 1) : d170803 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d125707, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37115 q ha hb
    | true =>
      simp only [d125707, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125708 q = 1) (hb : d169395 q = 1) : d170804 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d125708, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125708, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125709 q = 1) (hb : d169395 q = 1) : d170805 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d125709, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125709, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125710 q = 1) (hb : d169395 q = 1) : d170806 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d125710, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125710, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125711 q = 1) (hb : d169395 q = 1) : d170807 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d125711, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125711, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125712 q = 1) (hb : d169395 q = 1) : d170808 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d125712, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125712, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37117 (p : Pattern) (ha : d125718 p = 1) (hb : d169397 p = 1) : d170814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125713 q = 1) (hb : d169395 q = 1) : d170809 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d125713, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37116 q ha hb
    | true =>
      simp only [d125713, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125714 q = 1) (hb : d169395 q = 1) : d170810 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d125714, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125714, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125715 q = 1) (hb : d169395 q = 1) : d170811 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d125715, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125715, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125716 q = 1) (hb : d169395 q = 1) : d170812 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d125716, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125716, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125717 q = 1) (hb : d169395 q = 1) : d170813 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d125717, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125717, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d169396 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d125718 q = 1) (hb : d169397 q = 1) : d170814 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d125718, d169397, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125718, d169397, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro37118 (p : Pattern) (ha : d125724 p = 1) (hb : d169397 p = 1) : d170820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125719 q = 1) (hb : d169397 q = 1) : d170815 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d125719, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37117 q ha hb
    | true =>
      simp only [d125719, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125720 q = 1) (hb : d169397 q = 1) : d170816 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d125720, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125720, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125721 q = 1) (hb : d169397 q = 1) : d170817 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d125721, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125721, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125722 q = 1) (hb : d169397 q = 1) : d170818 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d125722, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125722, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125723 q = 1) (hb : d169397 q = 1) : d170819 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d125723, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125723, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125724 q = 1) (hb : d169397 q = 1) : d170820 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d125724, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125724, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37119 (p : Pattern) (ha : d125730 p = 1) (hb : d169397 p = 1) : d170826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125725 q = 1) (hb : d169397 q = 1) : d170821 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d125725, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37118 q ha hb
    | true =>
      simp only [d125725, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125726 q = 1) (hb : d169397 q = 1) : d170822 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d125726, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125726, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125727 q = 1) (hb : d169397 q = 1) : d170823 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d125727, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125727, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125728 q = 1) (hb : d169397 q = 1) : d170824 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d125728, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125728, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125729 q = 1) (hb : d169397 q = 1) : d170825 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d125729, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125729, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125730 q = 1) (hb : d169397 q = 1) : d170826 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d125730, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125730, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37120 (p : Pattern) (ha : d125736 p = 1) (hb : d169397 p = 1) : d170832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125731 q = 1) (hb : d169397 q = 1) : d170827 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d125731, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37119 q ha hb
    | true =>
      simp only [d125731, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125732 q = 1) (hb : d169397 q = 1) : d170828 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d125732, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125732, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125733 q = 1) (hb : d169397 q = 1) : d170829 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d125733, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125733, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125734 q = 1) (hb : d169397 q = 1) : d170830 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d125734, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125734, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125735 q = 1) (hb : d169397 q = 1) : d170831 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d125735, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125735, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125736 q = 1) (hb : d169397 q = 1) : d170832 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d125736, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125736, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37121 (p : Pattern) (ha : d125742 p = 1) (hb : d169397 p = 1) : d170838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d125737 q = 1) (hb : d169397 q = 1) : d170833 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d125737, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37120 q ha hb
    | true =>
      simp only [d125737, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d125738 q = 1) (hb : d169397 q = 1) : d170834 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d125738, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125738, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d125739 q = 1) (hb : d169397 q = 1) : d170835 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d125739, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d125739, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d125740 q = 1) (hb : d169397 q = 1) : d170836 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d125740, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d125740, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d125741 q = 1) (hb : d169397 q = 1) : d170837 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d125741, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d125741, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125742 q = 1) (hb : d169397 q = 1) : d170838 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d125742, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d125742, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37122 (p : Pattern) (ha : d146839 p = 1) (hb : d169398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d757 q = 1) (hb : d146838 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d146838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d146838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146839 q = 1) (hb : d169398 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146839, d169398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d146839, d169398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37123 (p : Pattern) (ha : d146845 p = 1) (hb : d169404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146840 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
    | true =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d146841 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146842 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d146843 q = 1) (hb : d169402 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146843, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146843, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d146844 q = 1) (hb : d169403 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d146844, d169403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146844, d169403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146845 q = 1) (hb : d169404 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d146845, d169404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146845, d169404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37124 (p : Pattern) (ha : d146851 p = 1) (hb : d169410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146850 q = 1) (hb : d169409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146850, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146850, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146851 q = 1) (hb : d169410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146851, d169410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146851, d169410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37125 (p : Pattern) (ha : d146857 p = 1) (hb : d169416 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d146852 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
    | true =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146853 q = 1) (hb : d169412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146853, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146853, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d146854 q = 1) (hb : d169413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146854, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146854, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146855 q = 1) (hb : d169414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146855, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d146855, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146856 q = 1) (hb : d169415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146856, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146856, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146857 q = 1) (hb : d169416 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146857, d169416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146857, d169416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37126 (p : Pattern) (ha : d146858 p = 1) (hb : d169417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146850 q = 1) (hb : d169409 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146850, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146850, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146858 q = 1) (hb : d169417 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146858, d169417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146858, d169417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37127 (p : Pattern) (ha : d146864 p = 1) (hb : d169423 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d146852 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
    | true =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146853 q = 1) (hb : d169412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146853, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146853, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d146854 q = 1) (hb : d169413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146854, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146854, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146855 q = 1) (hb : d169414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146855, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d146855, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146856 q = 1) (hb : d169415 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146856, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146856, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d146859 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37126 q ha hb
    | true =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d146860 q = 1) (hb : d169419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146860, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d146860, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d146861 q = 1) (hb : d169420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146861, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d146861, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d146862 q = 1) (hb : d169421 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146862, d169421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d146862, d169421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d146863 q = 1) (hb : d169422 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146863, d169422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d146863, d169422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d146864 q = 1) (hb : d169423 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146864, d169423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146864, d169423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro37128 (p : Pattern) (ha : d146871 p = 1) (hb : d169430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146859 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37126 q ha hb
    | true =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146860 q = 1) (hb : d169419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146860, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146860, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d146861 q = 1) (hb : d169420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146861, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146861, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146869 q = 1) (hb : d169428 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146869, d169428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146869, d169428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146870 q = 1) (hb : d169429 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146870, d169429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146870, d169429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146871 q = 1) (hb : d169430 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146871, d169430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146871, d169430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37129 (p : Pattern) (ha : d146878 p = 1) (hb : d169436 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d980 q = 1) (hb : d146877 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d146877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d146877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h10 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d146878 q = 1) (hb : d169436 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146878, d169436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d146878, d169436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37130 (p : Pattern) (ha : d146884 p = 1) (hb : d169442 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146879 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
    | true =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d146880 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146881 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d146882 q = 1) (hb : d169440 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146882, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146882, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h9 (q : Pattern) (ha : d146883 q = 1) (hb : d169441 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d146883, d169441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146883, d169441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146884 q = 1) (hb : d169442 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d146884, d169442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146884, d169442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37131 (p : Pattern) (ha : d146890 p = 1) (hb : d169448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146885 q = 1) (hb : d169443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146885, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37130 q ha hb
    | true =>
      simp only [d146885, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146886 q = 1) (hb : d169444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146886, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146886, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146887 q = 1) (hb : d169445 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146887, d169445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146887, d169445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146888 q = 1) (hb : d169446 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146888, d169446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146888, d169446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146889 q = 1) (hb : d169447 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146889, d169447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146889, d169447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146890 q = 1) (hb : d169448 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146890, d169448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146890, d169448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37132 (p : Pattern) (ha : d146896 p = 1) (hb : d169454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146891 q = 1) (hb : d169449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146891, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37131 q ha hb
    | true =>
      simp only [d146891, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146892 q = 1) (hb : d169450 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146892, d169450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146892, d169450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d146893 q = 1) (hb : d169451 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146893, d169451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146893, d169451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146894 q = 1) (hb : d169452 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146894, d169452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146894, d169452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146895 q = 1) (hb : d169453 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146895, d169453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146895, d169453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146896 q = 1) (hb : d169454 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146896, d169454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146896, d169454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37133 (p : Pattern) (ha : d146902 p = 1) (hb : d169460 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d146865 q = 1) (hb : d169424 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146865, d169424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37125 q ha hb
    | true =>
      simp only [d146865, d169424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37127 q ha hb
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
  have h8 (q : Pattern) (ha : d146866 q = 1) (hb : d169425 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146866, d169425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146866, d169425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d146867 q = 1) (hb : d169426 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146867, d169426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146867, d169426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146868 q = 1) (hb : d169427 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146868, d169427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d146868, d169427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146872 q = 1) (hb : d169431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146872, d169431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146872, d169431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37128 q ha hb
  have h12 (q : Pattern) (ha : d146873 q = 1) (hb : d169432 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146873, d169432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146873, d169432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146874 q = 1) (hb : d169433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146874, d169433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146874, d169433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146875 q = 1) (hb : d169434 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146875, d169434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146875, d169434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146876 q = 1) (hb : d169435 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146876, d169435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146876, d169435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146897 q = 1) (hb : d169455 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146897, d169455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146897, d169455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37132 q ha hb
  have h17 (q : Pattern) (ha : d146898 q = 1) (hb : d169456 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146898, d169456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d146898, d169456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d146899 q = 1) (hb : d169457 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146899, d169457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146899, d169457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d146900 q = 1) (hb : d169458 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146900, d169458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d146900, d169458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d146901 q = 1) (hb : d169459 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146901, d169459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d146901, d169459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d146902 q = 1) (hb : d169460 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d146902, d169460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146902, d169460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro37134 (p : Pattern) (ha : d146912 p = 1) (hb : d169470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146852 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
    | true =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d146908 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146908, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146908, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146909 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146909, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146909, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146910 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146910, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146910, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146911 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146911, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146911, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146912 q = 1) (hb : d169470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146912, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146912, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37135 (p : Pattern) (ha : d146919 p = 1) (hb : d169477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146852 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
    | true =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d146908 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146908, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146908, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146909 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146909, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146909, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146910 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146910, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146910, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146911 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146911, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146911, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146859 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37126 q ha hb
    | true =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d146915 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146915, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146915, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146916 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146916, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146916, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146917 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146917, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146917, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146918 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146918, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146918, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146919 q = 1) (hb : d169477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146919, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146919, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37136 (p : Pattern) (ha : d146924 p = 1) (hb : d169482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146923 q = 1) (hb : d169481 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146923, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146923, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146924 q = 1) (hb : d169482 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146924, d169482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146924, d169482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37137 (p : Pattern) (ha : d146931 p = 1) (hb : d169489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146929 q = 1) (hb : d169487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146929, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146929, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146930 q = 1) (hb : d169488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146930, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146930, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146931 q = 1) (hb : d169489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146931, d169489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146931, d169489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37138 (p : Pattern) (ha : d146942 p = 1) (hb : d169494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d146936 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28086 q ha hb
    | true =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d146937 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d146938 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d146938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d146938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d146939 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d146939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d146939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146940 q = 1) (hb : d169493 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d146940, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146940, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d5451 q = 1) (hb : d74177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d5452 q = 1) (hb : d74178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d5453 q = 1) (hb : d74179 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5453, d74179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d5454 q = 1) (hb : d74180 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5454, d74180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d5455 q = 1) (hb : d146941 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d146941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5455, d146941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146942 q = 1) (hb : d169494 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d146942, d169494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146942, d169494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro37139 (p : Pattern) (ha : d146948 p = 1) (hb : d169500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146943 q = 1) (hb : d169495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146943, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37138 q ha hb
    | true =>
      simp only [d146943, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
  have h2 (q : Pattern) (ha : d146944 q = 1) (hb : d169496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146944, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146944, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146945 q = 1) (hb : d169497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146945, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146945, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146840 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
    | true =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h5 (q : Pattern) (ha : d146841 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146842 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146946 q = 1) (hb : d169498 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146946, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146946, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d146843 q = 1) (hb : d169402 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146843, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146843, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d146947 q = 1) (hb : d169499 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d146947, d169499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146947, d169499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146948 q = 1) (hb : d169500 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d146948, d169500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d146948, d169500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37140 (p : Pattern) (ha : d146954 p = 1) (hb : d169506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146949 q = 1) (hb : d169501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146949, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37139 q ha hb
    | true =>
      simp only [d146949, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146950 q = 1) (hb : d169502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146950, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146950, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146951 q = 1) (hb : d169503 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146951, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146951, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146952 q = 1) (hb : d169504 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146952, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146952, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146953 q = 1) (hb : d169505 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146953, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146953, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146954 q = 1) (hb : d169506 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146954, d169506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146954, d169506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37141 (p : Pattern) (ha : d146960 p = 1) (hb : d169512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146957 q = 1) (hb : d169509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146957, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146957, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146958 q = 1) (hb : d169510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146958, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146958, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146959 q = 1) (hb : d169511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146959, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146959, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146960 q = 1) (hb : d169512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146960, d169512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146960, d169512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37142 (p : Pattern) (ha : d146966 p = 1) (hb : d169518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146925 q = 1) (hb : d169483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146925, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37136 q ha hb
    | true =>
      simp only [d146925, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d146926 q = 1) (hb : d169484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146926, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146926, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146927 q = 1) (hb : d169485 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146927, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146927, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146928 q = 1) (hb : d169486 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146928, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146928, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146932 q = 1) (hb : d169490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146932, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37137 q ha hb
    | true =>
      simp only [d146932, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d146933 q = 1) (hb : d169491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146933, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146933, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146934 q = 1) (hb : d169492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146934, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146934, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146955 q = 1) (hb : d169507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146955, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37140 q ha hb
    | true =>
      simp only [d146955, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146852 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146956 q = 1) (hb : d169508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146956, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d146961 q = 1) (hb : d169513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146961, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37141 q ha hb
    | true =>
      simp only [d146961, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146962 q = 1) (hb : d169514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146962, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146962, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146963 q = 1) (hb : d169515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146963, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146964 q = 1) (hb : d169516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146964, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146965 q = 1) (hb : d169517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146965, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146966 q = 1) (hb : d169518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146966, d169518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146966, d169518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37143 (p : Pattern) (ha : d146967 p = 1) (hb : d169519 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146849 q = 1) (hb : d169408 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146849, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146923 q = 1) (hb : d169481 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146923, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146923, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146967 q = 1) (hb : d169519 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146967, d169519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146967, d169519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37144 (p : Pattern) (ha : d146972 p = 1) (hb : d169524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146848 q = 1) (hb : d169407 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146848, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146929 q = 1) (hb : d169487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146929, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146929, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146930 q = 1) (hb : d169488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146930, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146930, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146972 q = 1) (hb : d169524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146972, d169524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146972, d169524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37145 (p : Pattern) (ha : d146976 p = 1) (hb : d169528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146949 q = 1) (hb : d169501 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146949, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37139 q ha hb
    | true =>
      simp only [d146949, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146950 q = 1) (hb : d169502 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146950, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146950, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146951 q = 1) (hb : d169503 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146951, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146951, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146952 q = 1) (hb : d169504 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146952, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146952, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146953 q = 1) (hb : d169505 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146953, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146953, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146976 q = 1) (hb : d169528 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146976, d169528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146976, d169528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37146 (p : Pattern) (ha : d146979 p = 1) (hb : d169531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146846 q = 1) (hb : d169405 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37123 q ha hb
    | true =>
      simp only [d146846, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146847 q = 1) (hb : d169406 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146847, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146957 q = 1) (hb : d169509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d146957, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146957, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146958 q = 1) (hb : d169510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d146958, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146958, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146959 q = 1) (hb : d169511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d146959, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146959, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146979 q = 1) (hb : d169531 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d146979, d169531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146979, d169531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37147 (p : Pattern) (ha : d146985 p = 1) (hb : d169537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146925 q = 1) (hb : d169483 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146925, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37136 q ha hb
    | true =>
      simp only [d146925, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d146926 q = 1) (hb : d169484 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146926, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146926, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146927 q = 1) (hb : d169485 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146927, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146927, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146928 q = 1) (hb : d169486 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146928, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146928, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146932 q = 1) (hb : d169490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146932, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37137 q ha hb
    | true =>
      simp only [d146932, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d146933 q = 1) (hb : d169491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146933, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146933, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146934 q = 1) (hb : d169492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146934, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146934, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146955 q = 1) (hb : d169507 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146955, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37140 q ha hb
    | true =>
      simp only [d146955, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146852 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d146956 q = 1) (hb : d169508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146956, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d146961 q = 1) (hb : d169513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146961, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37141 q ha hb
    | true =>
      simp only [d146961, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146962 q = 1) (hb : d169514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146962, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146962, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146963 q = 1) (hb : d169515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146963, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146964 q = 1) (hb : d169516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146964, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146965 q = 1) (hb : d169517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146965, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146968 q = 1) (hb : d169520 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146968, d169520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37143 q ha hb
    | true =>
      simp only [d146968, d169520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d146969 q = 1) (hb : d169521 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146969, d169521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146969, d169521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146970 q = 1) (hb : d169522 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146970, d169522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d146970, d169522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d146971 q = 1) (hb : d169523 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146971, d169523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146971, d169523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d146973 q = 1) (hb : d169525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146973, d169525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37144 q ha hb
    | true =>
      simp only [d146973, d169525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d146974 q = 1) (hb : d169526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146974, d169526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146974, d169526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d146975 q = 1) (hb : d169527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146975, d169527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d146975, d169527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d146977 q = 1) (hb : d169529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146977, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37145 q ha hb
    | true =>
      simp only [d146977, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37126 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d146859 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d146978 q = 1) (hb : d169530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d146978, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d146980 q = 1) (hb : d169532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146980, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37146 q ha hb
    | true =>
      simp only [d146980, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d146981 q = 1) (hb : d169533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146981, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d146981, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d146982 q = 1) (hb : d169534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d146982, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d146983 q = 1) (hb : d169535 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146983, d169535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d146983, d169535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d146984 q = 1) (hb : d169536 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146984, d169536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d146984, d169536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d146985 q = 1) (hb : d169537 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146985, d169537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d146985, d169537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro37148 (p : Pattern) (ha : d146987 p = 1) (hb : d169539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146852 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
    | true =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d146908 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146908, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146908, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146909 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146909, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146909, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146910 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146910, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146910, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146911 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146911, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146911, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d146987 q = 1) (hb : d169539 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146987, d169539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146987, d169539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro37149 (p : Pattern) (ha : d146994 p = 1) (hb : d169546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146977 q = 1) (hb : d169529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146977, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37145 q ha hb
    | true =>
      simp only [d146977, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37126 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146859 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146978 q = 1) (hb : d169530 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146978, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146980 q = 1) (hb : d169532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146980, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37146 q ha hb
    | true =>
      simp only [d146980, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146981 q = 1) (hb : d169533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146981, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146981, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146982 q = 1) (hb : d169534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146982, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146992 q = 1) (hb : d169544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146992, d169544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146992, d169544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146993 q = 1) (hb : d169545 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146993, d169545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146993, d169545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146994 q = 1) (hb : d169546 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146994, d169546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146994, d169546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37150 (p : Pattern) (ha : d147006 p = 1) (hb : d169553 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d147000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d147000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d147000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28086 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d146936 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28086 q ha hb
    | true =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d147001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d147001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d147001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d146937 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d147002 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d147002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d147002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d147003 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d147003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d147003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147004 q = 1) (hb : d169552 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147004, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147004, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d5495 q = 1) (hb : d74221 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5495, d74221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
  have h10 (q : Pattern) (ha : d5451 q = 1) (hb : d74177 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9259 q ha hb
    | true =>
      simp only [d5451, d74177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5496 q = 1) (hb : d74222 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d5496, d74222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5452 q = 1) (hb : d74178 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5452, d74178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5497 q = 1) (hb : d74223 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5497, d74223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d5498 q = 1) (hb : d74224 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5498, d74224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d5499 q = 1) (hb : d147005 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d147005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d5499, d147005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147006 q = 1) (hb : d169553 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147006, d169553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147006, d169553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro37151 (p : Pattern) (ha : d147012 p = 1) (hb : d169559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147007 q = 1) (hb : d169554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147007, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37150 q ha hb
    | true =>
      simp only [d147007, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
  have h2 (q : Pattern) (ha : d147008 q = 1) (hb : d169555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147008, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147008, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147009 q = 1) (hb : d169556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147009, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147009, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146879 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
    | true =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h5 (q : Pattern) (ha : d146880 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146881 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147010 q = 1) (hb : d169557 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147010, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147010, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d146882 q = 1) (hb : d169440 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146882, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146882, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d147011 q = 1) (hb : d169558 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147011, d169558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147011, d169558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147012 q = 1) (hb : d169559 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147012, d169559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147012, d169559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37152 (p : Pattern) (ha : d147018 p = 1) (hb : d169565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147013 q = 1) (hb : d169560 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147013, d169560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37151 q ha hb
    | true =>
      simp only [d147013, d169560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147014 q = 1) (hb : d169561 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147014, d169561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147014, d169561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146885 q = 1) (hb : d169443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146885, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37130 q ha hb
    | true =>
      simp only [d146885, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146886 q = 1) (hb : d169444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146886, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146886, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147015 q = 1) (hb : d169562 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147015, d169562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147015, d169562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147016 q = 1) (hb : d169563 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147016, d169563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147016, d169563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147017 q = 1) (hb : d169564 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147017, d169564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147017, d169564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147018 q = 1) (hb : d169565 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147018, d169565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147018, d169565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37153 (p : Pattern) (ha : d147024 p = 1) (hb : d169571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146885 q = 1) (hb : d169443 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d146885, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37130 q ha hb
    | true =>
      simp only [d146885, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146886 q = 1) (hb : d169444 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d146886, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146886, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147021 q = 1) (hb : d169568 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147021, d169568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147021, d169568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147022 q = 1) (hb : d169569 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147022, d169569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147022, d169569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147023 q = 1) (hb : d169570 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147023, d169570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147023, d169570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147024 q = 1) (hb : d169571 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147024, d169571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147024, d169571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37154 (p : Pattern) (ha : d147030 p = 1) (hb : d169577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147019 q = 1) (hb : d169566 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147019, d169566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37152 q ha hb
    | true =>
      simp only [d147019, d169566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37131 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146891 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147020 q = 1) (hb : d169567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147020, d169567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147020, d169567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147025 q = 1) (hb : d169572 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147025, d169572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37153 q ha hb
    | true =>
      simp only [d147025, d169572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147026 q = 1) (hb : d169573 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147026, d169573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147026, d169573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147027 q = 1) (hb : d169574 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147027, d169574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147027, d169574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147028 q = 1) (hb : d169575 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147028, d169575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147028, d169575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147029 q = 1) (hb : d169576 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147029, d169576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147029, d169576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147030 q = 1) (hb : d169577 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147030, d169577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147030, d169577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37155 (p : Pattern) (ha : d147036 p = 1) (hb : d169583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146913 q = 1) (hb : d169471 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146913, d169471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146913, d169471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37134 q ha hb
  have h2 (q : Pattern) (ha : d146914 q = 1) (hb : d169472 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146914, d169472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146914, d169472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146920 q = 1) (hb : d169478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146920, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37134 q ha hb
    | true =>
      simp only [d146920, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37135 q ha hb
  have h4 (q : Pattern) (ha : d146921 q = 1) (hb : d169479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146921, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146921, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146922 q = 1) (hb : d169480 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146922, d169480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d146922, d169480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146986 q = 1) (hb : d169538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146986, d169538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37142 q ha hb
    | true =>
      simp only [d146986, d169538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37147 q ha hb
  have h7 (q : Pattern) (ha : d146988 q = 1) (hb : d169540 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146988, d169540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37148 q ha hb
    | true =>
      simp only [d146988, d169540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d146989 q = 1) (hb : d169541 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146989, d169541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146989, d169541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146990 q = 1) (hb : d169542 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146990, d169542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146990, d169542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d146991 q = 1) (hb : d169543 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146991, d169543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146991, d169543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146995 q = 1) (hb : d169547 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146995, d169547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146995, d169547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37149 q ha hb
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
  have h13 (q : Pattern) (ha : d146996 q = 1) (hb : d169548 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146996, d169548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d146996, d169548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d146997 q = 1) (hb : d169549 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146997, d169549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146997, d169549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146998 q = 1) (hb : d169550 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146998, d169550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d146998, d169550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d146999 q = 1) (hb : d169551 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146999, d169551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146999, d169551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147031 q = 1) (hb : d169578 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147031, d169578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147031, d169578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37154 q ha hb
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
  have h19 (q : Pattern) (ha : d147032 q = 1) (hb : d169579 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147032, d169579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147032, d169579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d147033 q = 1) (hb : d169580 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147033, d169580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147033, d169580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147034 q = 1) (hb : d169581 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147034, d169581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147034, d169581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147035 q = 1) (hb : d169582 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147035, d169582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147035, d169582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147036 q = 1) (hb : d169583 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147036, d169583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147036, d169583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37156 (p : Pattern) (ha : d147042 p = 1) (hb : d169589 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d146903 q = 1) (hb : d169461 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d146903, d169461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146903, d169461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37133 q ha hb
  have h6 (q : Pattern) (ha : d146904 q = 1) (hb : d169462 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d146904, d169462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146904, d169462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146905 q = 1) (hb : d169463 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d146905, d169463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146905, d169463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146906 q = 1) (hb : d169464 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d146906, d169464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146906, d169464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146907 q = 1) (hb : d169465 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d146907, d169465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146907, d169465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147037 q = 1) (hb : d169584 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147037, d169584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147037, d169584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37155 q ha hb
  have h11 (q : Pattern) (ha : d147038 q = 1) (hb : d169585 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147038, d169585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147038, d169585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147039 q = 1) (hb : d169586 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147039, d169586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147039, d169586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147040 q = 1) (hb : d169587 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147040, d169587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147040, d169587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147041 q = 1) (hb : d169588 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147041, d169588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147041, d169588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147042 q = 1) (hb : d169589 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147042, d169589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147042, d169589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37157 (p : Pattern) (ha : d147045 p = 1) (hb : d169592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146943 q = 1) (hb : d169495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146943, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37138 q ha hb
    | true =>
      simp only [d146943, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
  have h2 (q : Pattern) (ha : d146944 q = 1) (hb : d169496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146944, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146944, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146945 q = 1) (hb : d169497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146945, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146945, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146840 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
    | true =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h5 (q : Pattern) (ha : d146841 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146842 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146946 q = 1) (hb : d169498 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146946, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146946, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147043 q = 1) (hb : d169590 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147043, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147043, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147044 q = 1) (hb : d169591 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147044, d169591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147044, d169591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147045 q = 1) (hb : d169592 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147045, d169592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147045, d169592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37158 (p : Pattern) (ha : d147049 p = 1) (hb : d169596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146840 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
    | true =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h2 (q : Pattern) (ha : d146841 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146842 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147043 q = 1) (hb : d169590 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147043, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147043, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147048 q = 1) (hb : d169595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147048, d169595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147048, d169595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147049 q = 1) (hb : d169596 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147049, d169596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147049, d169596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37159 (p : Pattern) (ha : d147055 p = 1) (hb : d169602 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147054 q = 1) (hb : d169601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147054, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147054, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147055 q = 1) (hb : d169602 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147055, d169602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147055, d169602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37160 (p : Pattern) (ha : d147059 p = 1) (hb : d169606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147058 q = 1) (hb : d169605 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147058, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147058, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147059 q = 1) (hb : d169606 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147059, d169606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147059, d169606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37161 (p : Pattern) (ha : d147065 p = 1) (hb : d169612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147060 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37159 q ha hb
    | true =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37160 q ha hb
  have h2 (q : Pattern) (ha : d147061 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147061, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147061, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147062 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147062, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147062, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147063 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147063, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147063, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147064 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147064, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147064, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147065 q = 1) (hb : d169612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147065, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147065, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37162 (p : Pattern) (ha : d147068 p = 1) (hb : d169615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147054 q = 1) (hb : d169601 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147054, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147054, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147068 q = 1) (hb : d169615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147068, d169615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147068, d169615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37163 (p : Pattern) (ha : d147069 p = 1) (hb : d169616 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147058 q = 1) (hb : d169605 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147058, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147058, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147069 q = 1) (hb : d169616 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147069, d169616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147069, d169616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37164 (p : Pattern) (ha : d147075 p = 1) (hb : d169622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147060 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37159 q ha hb
    | true =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37160 q ha hb
  have h2 (q : Pattern) (ha : d147061 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147061, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147061, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147062 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147062, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147062, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147063 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147063, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147063, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147064 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147064, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147064, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147070 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37162 q ha hb
    | true =>
      simp only [d147070, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37163 q ha hb
  have h7 (q : Pattern) (ha : d147071 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147071, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147071, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147072 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147072, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147072, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147073 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147073, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147073, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147074 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147074, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147074, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147075 q = 1) (hb : d169622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147075, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147075, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37165 (p : Pattern) (ha : d147080 p = 1) (hb : d169627 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147079 q = 1) (hb : d169626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147079, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147079, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147080 q = 1) (hb : d169627 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147080, d169627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147080, d169627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37166 (p : Pattern) (ha : d147082 p = 1) (hb : d169629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147081 q = 1) (hb : d169628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147081, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147081, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147082 q = 1) (hb : d169629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147082, d169629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147082, d169629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37167 (p : Pattern) (ha : d147089 p = 1) (hb : d169636 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147087 q = 1) (hb : d169634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147087, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147087, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147088 q = 1) (hb : d169635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147088, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147088, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147089 q = 1) (hb : d169636 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147089, d169636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147089, d169636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37168 (p : Pattern) (ha : d147092 p = 1) (hb : d169639 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147090 q = 1) (hb : d169637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147090, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147090, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147091 q = 1) (hb : d169638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147091, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147091, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147092 q = 1) (hb : d169639 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147092, d169639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147092, d169639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37169 (p : Pattern) (ha : d147108 p = 1) (hb : d169645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d147097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28118 q ha hb
    | true =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d147098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d147099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d147099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d147099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d147100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d147100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d147100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d146939 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147101 q = 1) (hb : d169643 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147101, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147101, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21189 q = 1) (hb : d147103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
    | true =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21190 q = 1) (hb : d147104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21191 q = 1) (hb : d147105 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d147105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d147105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21192 q = 1) (hb : d147106 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d147106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21192, d147106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d74180 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147107 q = 1) (hb : d169644 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147107, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147107, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d147108 q = 1) (hb : d169645 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147108, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147108, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro37170 (p : Pattern) (ha : d147112 p = 1) (hb : d169649 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5455 q = 1) (hb : d146941 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5455, d146941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5455, d146941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27 q = 1) (hb : d51879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27, d51879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d28 q = 1) (hb : d51880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d28, d51880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d29 q = 1) (hb : d51881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d29, d51881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d147112 q = 1) (hb : d169649 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147112, d169649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147112, d169649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37171 (p : Pattern) (ha : d147118 p = 1) (hb : d169655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147109 q = 1) (hb : d169646 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147109, d169646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37169 q ha hb
    | true =>
      simp only [d147109, d169646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37138 q ha hb
  have h2 (q : Pattern) (ha : d147110 q = 1) (hb : d169647 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147110, d169647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147110, d169647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147111 q = 1) (hb : d169648 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147111, d169648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147111, d169648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147113 q = 1) (hb : d169650 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147113, d169650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37138 q ha hb
    | true =>
      simp only [d147113, d169650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37170 q ha hb
  have h5 (q : Pattern) (ha : d147114 q = 1) (hb : d169651 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147114, d169651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147114, d169651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147115 q = 1) (hb : d169652 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147115, d169652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147115, d169652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147116 q = 1) (hb : d169653 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147116, d169653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147116, d169653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146943 q = 1) (hb : d169495 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146943, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37138 q ha hb
    | true =>
      simp only [d146943, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
  have h9 (q : Pattern) (ha : d146944 q = 1) (hb : d169496 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146944, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146944, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146945 q = 1) (hb : d169497 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146945, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146945, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146840 q = 1) (hb : d169399 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37122 q ha hb
    | true =>
      simp only [d146840, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q hb ha
  have h12 (q : Pattern) (ha : d146841 q = 1) (hb : d169400 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146841, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146842 q = 1) (hb : d169401 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146842, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146946 q = 1) (hb : d169498 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d146946, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146946, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147117 q = 1) (hb : d169654 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147117, d169654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147117, d169654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147118 q = 1) (hb : d169655 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147118, d169655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147118, d169655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37172 (p : Pattern) (ha : d147124 p = 1) (hb : d169661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147119 q = 1) (hb : d169656 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147119, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37171 q ha hb
    | true =>
      simp only [d147119, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147120 q = 1) (hb : d169657 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147120, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147120, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147121 q = 1) (hb : d169658 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147121, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147121, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147122 q = 1) (hb : d169659 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147122, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147122, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147123 q = 1) (hb : d169660 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147123, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147123, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147124 q = 1) (hb : d169661 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147124, d169661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147124, d169661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37173 (p : Pattern) (ha : d147130 p = 1) (hb : d169667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147127 q = 1) (hb : d169664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147127, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147127, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147128 q = 1) (hb : d169665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147128, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147128, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147129 q = 1) (hb : d169666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147129, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147129, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147130 q = 1) (hb : d169667 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147130, d169667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147130, d169667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37174 (p : Pattern) (ha : d147136 p = 1) (hb : d169673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147083 q = 1) (hb : d169630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147083, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37165 q ha hb
    | true =>
      simp only [d147083, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37166 q ha hb
  have h2 (q : Pattern) (ha : d147084 q = 1) (hb : d169631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147084, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147084, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147085 q = 1) (hb : d169632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147085, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147085, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147086 q = 1) (hb : d169633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147086, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147086, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147093 q = 1) (hb : d169640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147093, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37167 q ha hb
    | true =>
      simp only [d147093, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37168 q ha hb
  have h6 (q : Pattern) (ha : d147094 q = 1) (hb : d169641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147094, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147094, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147095 q = 1) (hb : d169642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147095, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147095, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147125 q = 1) (hb : d169662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147125, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37172 q ha hb
    | true =>
      simp only [d147125, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37159 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147060 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147126 q = 1) (hb : d169663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147126, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147131 q = 1) (hb : d169668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147131, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37173 q ha hb
    | true =>
      simp only [d147131, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147132 q = 1) (hb : d169669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147132, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147132, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147133 q = 1) (hb : d169670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147133, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147134 q = 1) (hb : d169671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147134, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147135 q = 1) (hb : d169672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147135, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147136 q = 1) (hb : d169673 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147136, d169673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147136, d169673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37175 (p : Pattern) (ha : d147137 p = 1) (hb : d169674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147053 q = 1) (hb : d169600 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147053, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147079 q = 1) (hb : d169626 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147079, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147079, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147137 q = 1) (hb : d169674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147137, d169674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147137, d169674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37176 (p : Pattern) (ha : d147138 p = 1) (hb : d169675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147057 q = 1) (hb : d169604 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147057, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147081 q = 1) (hb : d169628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147081, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147081, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147138 q = 1) (hb : d169675 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147138, d169675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147138, d169675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37177 (p : Pattern) (ha : d147143 p = 1) (hb : d169680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147052 q = 1) (hb : d169599 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147052, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147087 q = 1) (hb : d169634 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147087, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147087, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147088 q = 1) (hb : d169635 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147088, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147088, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147143 q = 1) (hb : d169680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147143, d169680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147143, d169680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37178 (p : Pattern) (ha : d147144 p = 1) (hb : d169681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147050 q = 1) (hb : d169597 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37158 q ha hb
    | true =>
      simp only [d147050, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147051 q = 1) (hb : d169598 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147051, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147056 q = 1) (hb : d169603 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147056, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147090 q = 1) (hb : d169637 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147090, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147090, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147091 q = 1) (hb : d169638 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147091, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147091, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147144 q = 1) (hb : d169681 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147144, d169681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147144, d169681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37179 (p : Pattern) (ha : d147148 p = 1) (hb : d169685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147119 q = 1) (hb : d169656 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147119, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37171 q ha hb
    | true =>
      simp only [d147119, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147120 q = 1) (hb : d169657 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147120, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147120, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147121 q = 1) (hb : d169658 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147121, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147121, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147122 q = 1) (hb : d169659 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147122, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147122, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147123 q = 1) (hb : d169660 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147123, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147123, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147148 q = 1) (hb : d169685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147148, d169685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147148, d169685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37180 (p : Pattern) (ha : d147151 p = 1) (hb : d169688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147046 q = 1) (hb : d169593 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37157 q ha hb
    | true =>
      simp only [d147046, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147047 q = 1) (hb : d169594 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147047, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147127 q = 1) (hb : d169664 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147127, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147127, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147128 q = 1) (hb : d169665 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147128, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147128, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147129 q = 1) (hb : d169666 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147129, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147129, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147151 q = 1) (hb : d169688 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147151, d169688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147151, d169688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37181 (p : Pattern) (ha : d147157 p = 1) (hb : d169694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147083 q = 1) (hb : d169630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147083, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37165 q ha hb
    | true =>
      simp only [d147083, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37166 q ha hb
  have h2 (q : Pattern) (ha : d147084 q = 1) (hb : d169631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147084, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147084, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147085 q = 1) (hb : d169632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147085, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147085, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147086 q = 1) (hb : d169633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147086, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147086, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147093 q = 1) (hb : d169640 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147093, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37167 q ha hb
    | true =>
      simp only [d147093, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37168 q ha hb
  have h6 (q : Pattern) (ha : d147094 q = 1) (hb : d169641 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147094, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147094, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147095 q = 1) (hb : d169642 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147095, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147095, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147125 q = 1) (hb : d169662 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147125, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37172 q ha hb
    | true =>
      simp only [d147125, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37159 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147060 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147126 q = 1) (hb : d169663 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147126, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147131 q = 1) (hb : d169668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147131, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37173 q ha hb
    | true =>
      simp only [d147131, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147132 q = 1) (hb : d169669 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147132, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147132, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147133 q = 1) (hb : d169670 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147133, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147134 q = 1) (hb : d169671 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147134, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147135 q = 1) (hb : d169672 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147135, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147139 q = 1) (hb : d169676 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147139, d169676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37175 q ha hb
    | true =>
      simp only [d147139, d169676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37176 q ha hb
  have h17 (q : Pattern) (ha : d147140 q = 1) (hb : d169677 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147140, d169677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147140, d169677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147141 q = 1) (hb : d169678 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147141, d169678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147141, d169678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d147142 q = 1) (hb : d169679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147142, d169679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147142, d169679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147145 q = 1) (hb : d169682 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147145, d169682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37177 q ha hb
    | true =>
      simp only [d147145, d169682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37178 q ha hb
  have h21 (q : Pattern) (ha : d147146 q = 1) (hb : d169683 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147146, d169683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147146, d169683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d147147 q = 1) (hb : d169684 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147147, d169684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147147, d169684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147149 q = 1) (hb : d169686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147149, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37179 q ha hb
    | true =>
      simp only [d147149, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37162 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147070 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d147150 q = 1) (hb : d169687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d147150, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d147152 q = 1) (hb : d169689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147152, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37180 q ha hb
    | true =>
      simp only [d147152, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d147153 q = 1) (hb : d169690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147153, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d147153, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d147154 q = 1) (hb : d169691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d147154, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d147155 q = 1) (hb : d169692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147155, d169692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d147155, d169692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d147156 q = 1) (hb : d169693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147156, d169693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147156, d169693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d147157 q = 1) (hb : d169694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147157, d169694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147157, d169694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro37182 (p : Pattern) (ha : d147164 p = 1) (hb : d169701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147060 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37159 q ha hb
    | true =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37160 q ha hb
  have h2 (q : Pattern) (ha : d147061 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147061, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147061, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147062 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147062, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147062, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147063 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147063, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147063, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147064 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147064, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147064, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147159 q = 1) (hb : d169696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147159, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37160 q ha hb
    | true =>
      simp only [d147159, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147160 q = 1) (hb : d169697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147160, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147160, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147161 q = 1) (hb : d169698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147161, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147161, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147162 q = 1) (hb : d169699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147162, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147162, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147163 q = 1) (hb : d169700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147163, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147163, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147164 q = 1) (hb : d169701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147164, d169701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147164, d169701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37183 (p : Pattern) (ha : d147170 p = 1) (hb : d169707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147159 q = 1) (hb : d169696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147159, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37160 q ha hb
    | true =>
      simp only [d147159, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147160 q = 1) (hb : d169697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147160, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147160, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147161 q = 1) (hb : d169698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147161, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147161, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147162 q = 1) (hb : d169699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147162, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147162, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147163 q = 1) (hb : d169700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147163, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147163, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147165 q = 1) (hb : d169702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147165, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37163 q ha hb
    | true =>
      simp only [d147165, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147166 q = 1) (hb : d169703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147166, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147166, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147167 q = 1) (hb : d169704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147167, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147167, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147168 q = 1) (hb : d169705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147168, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147168, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147169 q = 1) (hb : d169706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147169, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147169, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147170 q = 1) (hb : d169707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147170, d169707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147170, d169707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37184 (p : Pattern) (ha : d147177 p = 1) (hb : d169714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147149 q = 1) (hb : d169686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147149, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37179 q ha hb
    | true =>
      simp only [d147149, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37162 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147150 q = 1) (hb : d169687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147150, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147152 q = 1) (hb : d169689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147152, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37180 q ha hb
    | true =>
      simp only [d147152, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147153 q = 1) (hb : d169690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147153, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147153, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147154 q = 1) (hb : d169691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147154, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147175 q = 1) (hb : d169712 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147175, d169712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147175, d169712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147176 q = 1) (hb : d169713 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147176, d169713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147176, d169713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147177 q = 1) (hb : d169714 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147177, d169714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147177, d169714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37185 (p : Pattern) (ha : d147179 p = 1) (hb : d169716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147165 q = 1) (hb : d169702 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147165, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37163 q ha hb
    | true =>
      simp only [d147165, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147166 q = 1) (hb : d169703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147166, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147166, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147167 q = 1) (hb : d169704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147167, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147167, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147168 q = 1) (hb : d169705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147168, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147168, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147169 q = 1) (hb : d169706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147169, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147169, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147179 q = 1) (hb : d169716 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147179, d169716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147179, d169716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37186 (p : Pattern) (ha : d147195 p = 1) (hb : d169724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d147185 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d147185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d147185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28118 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d147097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28118 q ha hb
    | true =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d147186 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d147186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d147186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d147098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d147187 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d147187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d147187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d147188 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d147188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d147188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d147003 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147189 q = 1) (hb : d169722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147189, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147189, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d21314 q = 1) (hb : d147190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d147190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d147190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
  have h10 (q : Pattern) (ha : d21189 q = 1) (hb : d147103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
    | true =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21315 q = 1) (hb : d147191 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d147191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21315, d147191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21190 q = 1) (hb : d147104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21316 q = 1) (hb : d147192 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d147192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21316, d147192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21317 q = 1) (hb : d147193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d147193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21317, d147193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d74224 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d147194 q = 1) (hb : d169723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147194, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d147194, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d147195 q = 1) (hb : d169724 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147195, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147195, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro37187 (p : Pattern) (ha : d147199 p = 1) (hb : d169728 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d5499 q = 1) (hb : d147005 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5499, d147005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5499, d147005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d66 q = 1) (hb : d51918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d51918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
  have h10 (q : Pattern) (ha : d25 q = 1) (hb : d51877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro2 q ha hb
    | true =>
      simp only [d25, d51877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d67 q = 1) (hb : d51919 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d67, d51919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26 q = 1) (hb : d51878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26, d51878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d68 q = 1) (hb : d51920 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68, d51920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d69 q = 1) (hb : d51921 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d69, d51921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d70 q = 1) (hb : d51922 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d70, d51922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d147199 q = 1) (hb : d169728 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147199, d169728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d147199, d169728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37188 (p : Pattern) (ha : d147205 p = 1) (hb : d169734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147196 q = 1) (hb : d169725 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147196, d169725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37186 q ha hb
    | true =>
      simp only [d147196, d169725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37150 q ha hb
  have h2 (q : Pattern) (ha : d147197 q = 1) (hb : d169726 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147197, d169726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147197, d169726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147198 q = 1) (hb : d169727 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147198, d169727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147198, d169727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147200 q = 1) (hb : d169729 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147200, d169729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37150 q ha hb
    | true =>
      simp only [d147200, d169729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37187 q ha hb
  have h5 (q : Pattern) (ha : d147201 q = 1) (hb : d169730 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147201, d169730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147201, d169730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147202 q = 1) (hb : d169731 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147202, d169731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147202, d169731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147203 q = 1) (hb : d169732 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147203, d169732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147203, d169732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147007 q = 1) (hb : d169554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147007, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37150 q ha hb
    | true =>
      simp only [d147007, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
  have h9 (q : Pattern) (ha : d147008 q = 1) (hb : d169555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147008, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147008, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147009 q = 1) (hb : d169556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147009, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147009, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146879 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
    | true =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h12 (q : Pattern) (ha : d146880 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146881 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147010 q = 1) (hb : d169557 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147010, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147010, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147204 q = 1) (hb : d169733 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147204, d169733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147204, d169733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147205 q = 1) (hb : d169734 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147205, d169734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147205, d169734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37189 (p : Pattern) (ha : d147210 p = 1) (hb : d169739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147007 q = 1) (hb : d169554 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147007, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37150 q ha hb
    | true =>
      simp only [d147007, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
  have h2 (q : Pattern) (ha : d147008 q = 1) (hb : d169555 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147008, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147008, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147009 q = 1) (hb : d169556 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147009, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147009, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146879 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
    | true =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h5 (q : Pattern) (ha : d146880 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146881 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147010 q = 1) (hb : d169557 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147010, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147010, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147208 q = 1) (hb : d169737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147208, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147208, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147209 q = 1) (hb : d169738 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147209, d169738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147209, d169738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147210 q = 1) (hb : d169739 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147210, d169739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147210, d169739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37190 (p : Pattern) (ha : d147216 p = 1) (hb : d169745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147206 q = 1) (hb : d169735 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147206, d169735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37188 q ha hb
    | true =>
      simp only [d147206, d169735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147207 q = 1) (hb : d169736 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147207, d169736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147207, d169736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147211 q = 1) (hb : d169740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147211, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37189 q ha hb
    | true =>
      simp only [d147211, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147212 q = 1) (hb : d169741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147212, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147212, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147213 q = 1) (hb : d169742 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147213, d169742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147213, d169742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147214 q = 1) (hb : d169743 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147214, d169743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147214, d169743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147215 q = 1) (hb : d169744 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147215, d169744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147215, d169744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147216 q = 1) (hb : d169745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147216, d169745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147216, d169745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37191 (p : Pattern) (ha : d147218 p = 1) (hb : d169747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146879 q = 1) (hb : d169437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37129 q ha hb
    | true =>
      simp only [d146879, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q hb ha
  have h2 (q : Pattern) (ha : d146880 q = 1) (hb : d169438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146880, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146881 q = 1) (hb : d169439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146881, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147208 q = 1) (hb : d169737 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147208, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147208, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147217 q = 1) (hb : d169746 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147217, d169746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147217, d169746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147218 q = 1) (hb : d169747 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147218, d169747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147218, d169747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37192 (p : Pattern) (ha : d147224 p = 1) (hb : d169753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147211 q = 1) (hb : d169740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147211, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37189 q ha hb
    | true =>
      simp only [d147211, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147212 q = 1) (hb : d169741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147212, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147212, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147219 q = 1) (hb : d169748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147219, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37191 q ha hb
    | true =>
      simp only [d147219, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147220 q = 1) (hb : d169749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147220, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147220, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147221 q = 1) (hb : d169750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147221, d169750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147221, d169750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147222 q = 1) (hb : d169751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147222, d169751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147222, d169751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147223 q = 1) (hb : d169752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147223, d169752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147223, d169752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147224 q = 1) (hb : d169753 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147224, d169753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147224, d169753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37193 (p : Pattern) (ha : d147235 p = 1) (hb : d169759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147211 q = 1) (hb : d169740 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147211, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37189 q ha hb
    | true =>
      simp only [d147211, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147212 q = 1) (hb : d169741 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147212, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147212, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147232 q = 1) (hb : d169756 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147232, d169756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147232, d169756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147233 q = 1) (hb : d169757 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147233, d169757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147233, d169757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147234 q = 1) (hb : d169758 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147234, d169758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147234, d169758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147235 q = 1) (hb : d169759 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147235, d169759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147235, d169759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37194 (p : Pattern) (ha : d147241 p = 1) (hb : d169765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147225 q = 1) (hb : d169754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147225, d169754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37190 q ha hb
    | true =>
      simp only [d147225, d169754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37192 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147230 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147231 q = 1) (hb : d169755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147231, d169755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147231, d169755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147236 q = 1) (hb : d169760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147236, d169760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37193 q ha hb
    | true =>
      simp only [d147236, d169760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147237 q = 1) (hb : d169761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147237, d169761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147237, d169761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147238 q = 1) (hb : d169762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147238, d169762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147238, d169762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147239 q = 1) (hb : d169763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147239, d169763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147239, d169763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147240 q = 1) (hb : d169764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147240, d169764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147240, d169764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147241 q = 1) (hb : d169765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147241, d169765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147241, d169765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37195 (p : Pattern) (ha : d147229 p = 1) (hb : d169770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147219 q = 1) (hb : d169748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147219, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37191 q ha hb
    | true =>
      simp only [d147219, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147220 q = 1) (hb : d169749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147220, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147220, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147226 q = 1) (hb : d169767 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147226, d169767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147226, d169767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147227 q = 1) (hb : d169768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147227, d169768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147227, d169768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147228 q = 1) (hb : d169769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147228, d169769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147228, d169769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147229 q = 1) (hb : d169770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147229, d169770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147229, d169770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37196 (p : Pattern) (ha : d147248 p = 1) (hb : d169776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147243 q = 1) (hb : d169771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147243, d169771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37195 q ha hb
    | true =>
      simp only [d147243, d169771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147244 q = 1) (hb : d169772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147244, d169772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147244, d169772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147245 q = 1) (hb : d169773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147245, d169773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147245, d169773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147246 q = 1) (hb : d169774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147246, d169774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147246, d169774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147247 q = 1) (hb : d169775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147247, d169775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147247, d169775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147248 q = 1) (hb : d169776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147248, d169776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147248, d169776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37197 (p : Pattern) (ha : d147254 p = 1) (hb : d169782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147066 q = 1) (hb : d169613 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147066, d169613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147066, d169613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37161 q ha hb
  have h2 (q : Pattern) (ha : d147067 q = 1) (hb : d169614 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147067, d169614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147067, d169614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147076 q = 1) (hb : d169623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147076, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37161 q ha hb
    | true =>
      simp only [d147076, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37164 q ha hb
  have h4 (q : Pattern) (ha : d147077 q = 1) (hb : d169624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147077, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147077, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147078 q = 1) (hb : d169625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147078, d169625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147078, d169625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147158 q = 1) (hb : d169695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147158, d169695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37174 q ha hb
    | true =>
      simp only [d147158, d169695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37181 q ha hb
  have h7 (q : Pattern) (ha : d147171 q = 1) (hb : d169708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147171, d169708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37182 q ha hb
    | true =>
      simp only [d147171, d169708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37183 q ha hb
  have h8 (q : Pattern) (ha : d147172 q = 1) (hb : d169709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147172, d169709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147172, d169709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147173 q = 1) (hb : d169710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147173, d169710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147173, d169710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d147174 q = 1) (hb : d169711 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147174, d169711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147174, d169711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147178 q = 1) (hb : d169715 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147178, d169715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147178, d169715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37184 q ha hb
  have h12 (q : Pattern) (ha : d147180 q = 1) (hb : d169717 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147180, d169717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147180, d169717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37185 q ha hb
  have h13 (q : Pattern) (ha : d147181 q = 1) (hb : d169718 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147181, d169718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147181, d169718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147182 q = 1) (hb : d169719 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147182, d169719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147182, d169719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d147183 q = 1) (hb : d169720 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147183, d169720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d147183, d169720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d147184 q = 1) (hb : d169721 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147184, d169721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147184, d169721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147242 q = 1) (hb : d169766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147242, d169766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147242, d169766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37194 q ha hb
  have h18 (q : Pattern) (ha : d147249 q = 1) (hb : d169777 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147249, d169777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147249, d169777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37196 q ha hb
  have h19 (q : Pattern) (ha : d147250 q = 1) (hb : d169778 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147250, d169778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147250, d169778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147251 q = 1) (hb : d169779 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147251, d169779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147251, d169779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147252 q = 1) (hb : d169780 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147252, d169780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147252, d169780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147253 q = 1) (hb : d169781 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147253, d169781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147253, d169781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147254 q = 1) (hb : d169782 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147254, d169782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147254, d169782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37198 (p : Pattern) (ha : d147260 p = 1) (hb : d169788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147255 q = 1) (hb : d169783 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147255, d169783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147255, d169783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37197 q ha hb
  have h2 (q : Pattern) (ha : d147256 q = 1) (hb : d169784 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147256, d169784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147256, d169784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147257 q = 1) (hb : d169785 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147257, d169785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147257, d169785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147258 q = 1) (hb : d169786 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147258, d169786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147258, d169786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147259 q = 1) (hb : d169787 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147259, d169787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147259, d169787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147260 q = 1) (hb : d169788 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147260, d169788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147260, d169788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37199 (p : Pattern) (ha : d147263 p = 1) (hb : d169645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21183 q = 1) (hb : d147097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28118 q ha hb
    | true =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21184 q = 1) (hb : d147098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21185 q = 1) (hb : d147099 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21185, d147099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21185, d147099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21186 q = 1) (hb : d147100 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21186, d147100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21186, d147100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d146939 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147101 q = 1) (hb : d169643 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147101, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147101, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21189 q = 1) (hb : d147103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
    | true =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21190 q = 1) (hb : d147104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21191 q = 1) (hb : d147105 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21191, d147105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21191, d147105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21192 q = 1) (hb : d147106 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21192, d147106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21192, d147106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147262 q = 1) (hb : d169644 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147262, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147262, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d147263 q = 1) (hb : d169645 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147263, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147263, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro37200 (p : Pattern) (ha : d147264 p = 1) (hb : d169790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20990 q = 1) (hb : d146936 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28086 q ha hb
    | true =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20991 q = 1) (hb : d146937 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20992 q = 1) (hb : d146938 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d20992, d146938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20992, d146938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20993 q = 1) (hb : d146939 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d20993, d146939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20993, d146939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146940 q = 1) (hb : d169493 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d146940, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146940, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d757 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d147264 q = 1) (hb : d169790 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147264, d169790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147264, d169790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37201 (p : Pattern) (ha : d147274 p = 1) (hb : d169800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147265 q = 1) (hb : d169791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147265, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37199 q ha hb
    | true =>
      simp only [d147265, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37200 q ha hb
  have h2 (q : Pattern) (ha : d147266 q = 1) (hb : d169792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147266, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147266, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147267 q = 1) (hb : d169793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147267, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147267, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147268 q = 1) (hb : d169794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147268, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37200 q ha hb
    | true =>
      simp only [d147268, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h5 (q : Pattern) (ha : d147269 q = 1) (hb : d169795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147269, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147269, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147270 q = 1) (hb : d169796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147270, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147270, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147271 q = 1) (hb : d169797 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147271, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147271, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147272 q = 1) (hb : d169798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147272, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147272, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147273 q = 1) (hb : d169799 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147273, d169799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147273, d169799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147274 q = 1) (hb : d169800 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147274, d169800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147274, d169800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37202 (p : Pattern) (ha : d147278 p = 1) (hb : d169804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147268 q = 1) (hb : d169794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147268, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37200 q ha hb
    | true =>
      simp only [d147268, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h2 (q : Pattern) (ha : d147269 q = 1) (hb : d169795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147269, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147269, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147270 q = 1) (hb : d169796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147270, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147270, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147272 q = 1) (hb : d169798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147272, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147272, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147277 q = 1) (hb : d169803 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147277, d169803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147277, d169803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147278 q = 1) (hb : d169804 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147278, d169804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147278, d169804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37203 (p : Pattern) (ha : d147284 p = 1) (hb : d169810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147283 q = 1) (hb : d169809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147283, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147283, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147284 q = 1) (hb : d169810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147284, d169810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147284, d169810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37204 (p : Pattern) (ha : d147288 p = 1) (hb : d169814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147287 q = 1) (hb : d169813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147287, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147287, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147288 q = 1) (hb : d169814 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147288, d169814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147288, d169814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37205 (p : Pattern) (ha : d147294 p = 1) (hb : d169820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147289 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37203 q ha hb
    | true =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37204 q ha hb
  have h2 (q : Pattern) (ha : d147290 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147290, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147290, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147291 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147291, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147291, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147292 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147292, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147292, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147293 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147293, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147293, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147294 q = 1) (hb : d169820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147294, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147294, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37206 (p : Pattern) (ha : d147297 p = 1) (hb : d169823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147283 q = 1) (hb : d169809 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147283, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147283, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147297 q = 1) (hb : d169823 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147297, d169823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147297, d169823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37207 (p : Pattern) (ha : d147298 p = 1) (hb : d169824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147287 q = 1) (hb : d169813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147287, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147287, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147298 q = 1) (hb : d169824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147298, d169824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147298, d169824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37208 (p : Pattern) (ha : d147304 p = 1) (hb : d169830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147289 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37203 q ha hb
    | true =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37204 q ha hb
  have h2 (q : Pattern) (ha : d147290 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147290, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147290, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147291 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147291, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147291, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147292 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147292, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147292, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147293 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147293, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147293, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147299 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37206 q ha hb
    | true =>
      simp only [d147299, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37207 q ha hb
  have h7 (q : Pattern) (ha : d147300 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147300, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147300, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147301 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147301, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147301, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147302 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147302, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147302, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147303 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147303, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147303, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147304 q = 1) (hb : d169830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147304, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147304, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37209 (p : Pattern) (ha : d147309 p = 1) (hb : d169835 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147308 q = 1) (hb : d169834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147308, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147308, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147309 q = 1) (hb : d169835 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147309, d169835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147309, d169835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37210 (p : Pattern) (ha : d147311 p = 1) (hb : d169837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147310 q = 1) (hb : d169836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147310, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147310, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147311 q = 1) (hb : d169837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147311, d169837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147311, d169837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37211 (p : Pattern) (ha : d147318 p = 1) (hb : d169844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147316 q = 1) (hb : d169842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147316, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147316, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147317 q = 1) (hb : d169843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147317, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147317, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147318 q = 1) (hb : d169844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147318, d169844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147318, d169844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37212 (p : Pattern) (ha : d147321 p = 1) (hb : d169847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147319 q = 1) (hb : d169845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147319, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147319, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147320 q = 1) (hb : d169846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147320, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147320, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147321 q = 1) (hb : d169847 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147321, d169847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147321, d169847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37213 (p : Pattern) (ha : d21487 p = 1) (hb : d147331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d52278 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d531, d52278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d532 q = 1) (hb : d52279 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d52279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9581 q = 1) (hb : d101161 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9582 q = 1) (hb : d101162 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9593 q = 1) (hb : d101173 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d101173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9593, d101173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9594 q = 1) (hb : d101174 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d101174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9594, d101174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9595 q = 1) (hb : d101175 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d101175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9595, d101175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21487 q = 1) (hb : d147331 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21487, d147331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21487, d147331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37214 (p : Pattern) (ha : d147337 p = 1) (hb : d169853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21482 q = 1) (hb : d147326 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d147326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28161 q ha hb
    | true =>
      simp only [d21482, d147326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21483 q = 1) (hb : d147327 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d147327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21483, d147327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21484 q = 1) (hb : d147328 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21484, d147328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21484, d147328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21485 q = 1) (hb : d147329 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21485, d147329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21485, d147329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147100 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147330 q = 1) (hb : d169851 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147330, d169851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147330, d169851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21488 q = 1) (hb : d147332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d147332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37213 q ha hb
    | true =>
      simp only [d21488, d147332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21489 q = 1) (hb : d147333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d147333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21489, d147333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21490 q = 1) (hb : d147334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21490, d147334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21490, d147334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21491 q = 1) (hb : d147335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21491, d147335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21491, d147335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147106 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147336 q = 1) (hb : d169852 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147336, d169852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147336, d169852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d147337 q = 1) (hb : d169853 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147337, d169853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147337, d169853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro37215 (p : Pattern) (ha : d147341 p = 1) (hb : d169857 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147262 q = 1) (hb : d169644 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147262, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147262, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d753 q = 1) (hb : d52430 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d52430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d754 q = 1) (hb : d52431 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d754, d52431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d757 q = 1) (hb : d52434 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d757, d52434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d147341 q = 1) (hb : d169857 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147341, d169857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147341, d169857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37216 (p : Pattern) (ha : d147347 p = 1) (hb : d169863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147338 q = 1) (hb : d169854 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147338, d169854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37214 q ha hb
    | true =>
      simp only [d147338, d169854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37199 q ha hb
  have h2 (q : Pattern) (ha : d147339 q = 1) (hb : d169855 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147339, d169855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147339, d169855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147340 q = 1) (hb : d169856 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147340, d169856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147340, d169856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147342 q = 1) (hb : d169858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147342, d169858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37199 q ha hb
    | true =>
      simp only [d147342, d169858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37215 q ha hb
  have h5 (q : Pattern) (ha : d147343 q = 1) (hb : d169859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147343, d169859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147343, d169859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147344 q = 1) (hb : d169860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147344, d169860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147344, d169860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147345 q = 1) (hb : d169861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147345, d169861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147345, d169861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147265 q = 1) (hb : d169791 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147265, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37199 q ha hb
    | true =>
      simp only [d147265, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37200 q ha hb
  have h9 (q : Pattern) (ha : d147266 q = 1) (hb : d169792 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147266, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147266, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147267 q = 1) (hb : d169793 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147267, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147267, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147268 q = 1) (hb : d169794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147268, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37200 q ha hb
    | true =>
      simp only [d147268, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro103 q hb ha
  have h12 (q : Pattern) (ha : d147269 q = 1) (hb : d169795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147269, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147269, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147270 q = 1) (hb : d169796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147270, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147270, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147271 q = 1) (hb : d169797 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147271, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147271, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147346 q = 1) (hb : d169862 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147346, d169862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147346, d169862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147347 q = 1) (hb : d169863 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147347, d169863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147347, d169863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37217 (p : Pattern) (ha : d147353 p = 1) (hb : d169869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147348 q = 1) (hb : d169864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147348, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37216 q ha hb
    | true =>
      simp only [d147348, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147349 q = 1) (hb : d169865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147349, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147349, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147350 q = 1) (hb : d169866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147350, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147350, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147351 q = 1) (hb : d169867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147351, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147351, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147352 q = 1) (hb : d169868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147352, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147352, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147353 q = 1) (hb : d169869 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147353, d169869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147353, d169869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37218 (p : Pattern) (ha : d147359 p = 1) (hb : d169875 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147356 q = 1) (hb : d169872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147356, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147356, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147357 q = 1) (hb : d169873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147357, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147357, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147358 q = 1) (hb : d169874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147358, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147358, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147359 q = 1) (hb : d169875 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147359, d169875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147359, d169875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37219 (p : Pattern) (ha : d147365 p = 1) (hb : d169881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147312 q = 1) (hb : d169838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147312, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37209 q ha hb
    | true =>
      simp only [d147312, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37210 q ha hb
  have h2 (q : Pattern) (ha : d147313 q = 1) (hb : d169839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147313, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147313, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147314 q = 1) (hb : d169840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147314, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147314, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147315 q = 1) (hb : d169841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147315, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147315, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147322 q = 1) (hb : d169848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147322, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37211 q ha hb
    | true =>
      simp only [d147322, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37212 q ha hb
  have h6 (q : Pattern) (ha : d147323 q = 1) (hb : d169849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147323, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147323, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147324 q = 1) (hb : d169850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147324, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147324, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147354 q = 1) (hb : d169870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147354, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37217 q ha hb
    | true =>
      simp only [d147354, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37203 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147355 q = 1) (hb : d169871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147355, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147360 q = 1) (hb : d169876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147360, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37218 q ha hb
    | true =>
      simp only [d147360, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147361 q = 1) (hb : d169877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147361, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147361, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147362 q = 1) (hb : d169878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147362, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147363 q = 1) (hb : d169879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147363, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147364 q = 1) (hb : d169880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147364, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147365 q = 1) (hb : d169881 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147365, d169881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147365, d169881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37220 (p : Pattern) (ha : d147366 p = 1) (hb : d169882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147282 q = 1) (hb : d169808 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147282, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147308 q = 1) (hb : d169834 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147308, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147308, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147366 q = 1) (hb : d169882 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147366, d169882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147366, d169882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37221 (p : Pattern) (ha : d147367 p = 1) (hb : d169883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147286 q = 1) (hb : d169812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147286, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147310 q = 1) (hb : d169836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147310, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147310, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147367 q = 1) (hb : d169883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147367, d169883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147367, d169883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37222 (p : Pattern) (ha : d147372 p = 1) (hb : d169888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147281 q = 1) (hb : d169807 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147281, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147316 q = 1) (hb : d169842 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147316, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147316, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147317 q = 1) (hb : d169843 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147317, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147317, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147372 q = 1) (hb : d169888 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147372, d169888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147372, d169888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37223 (p : Pattern) (ha : d147373 p = 1) (hb : d169889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147279 q = 1) (hb : d169805 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37202 q ha hb
    | true =>
      simp only [d147279, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147280 q = 1) (hb : d169806 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147280, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147285 q = 1) (hb : d169811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147285, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147319 q = 1) (hb : d169845 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147319, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147319, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147320 q = 1) (hb : d169846 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147320, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147320, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147373 q = 1) (hb : d169889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147373, d169889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147373, d169889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37224 (p : Pattern) (ha : d147377 p = 1) (hb : d169893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147348 q = 1) (hb : d169864 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147348, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37216 q ha hb
    | true =>
      simp only [d147348, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147349 q = 1) (hb : d169865 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147349, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147349, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147350 q = 1) (hb : d169866 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147350, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147350, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147351 q = 1) (hb : d169867 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147351, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147351, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147352 q = 1) (hb : d169868 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147352, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147352, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147377 q = 1) (hb : d169893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147377, d169893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147377, d169893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37225 (p : Pattern) (ha : d147380 p = 1) (hb : d169896 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147275 q = 1) (hb : d169801 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37201 q ha hb
    | true =>
      simp only [d147275, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147276 q = 1) (hb : d169802 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147276, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147356 q = 1) (hb : d169872 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147356, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147356, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147357 q = 1) (hb : d169873 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147357, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147357, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147358 q = 1) (hb : d169874 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147358, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147358, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147380 q = 1) (hb : d169896 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147380, d169896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147380, d169896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37226 (p : Pattern) (ha : d147386 p = 1) (hb : d169902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147312 q = 1) (hb : d169838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147312, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37209 q ha hb
    | true =>
      simp only [d147312, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37210 q ha hb
  have h2 (q : Pattern) (ha : d147313 q = 1) (hb : d169839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147313, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147313, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147314 q = 1) (hb : d169840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147314, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147314, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147315 q = 1) (hb : d169841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147315, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147315, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147322 q = 1) (hb : d169848 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147322, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37211 q ha hb
    | true =>
      simp only [d147322, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37212 q ha hb
  have h6 (q : Pattern) (ha : d147323 q = 1) (hb : d169849 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147323, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147323, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147324 q = 1) (hb : d169850 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147324, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147324, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147354 q = 1) (hb : d169870 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147354, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37217 q ha hb
    | true =>
      simp only [d147354, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37203 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147355 q = 1) (hb : d169871 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147355, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147360 q = 1) (hb : d169876 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147360, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37218 q ha hb
    | true =>
      simp only [d147360, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147361 q = 1) (hb : d169877 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147361, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147361, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147362 q = 1) (hb : d169878 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147362, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147363 q = 1) (hb : d169879 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147363, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147364 q = 1) (hb : d169880 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147364, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147368 q = 1) (hb : d169884 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147368, d169884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37220 q ha hb
    | true =>
      simp only [d147368, d169884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37221 q ha hb
  have h17 (q : Pattern) (ha : d147369 q = 1) (hb : d169885 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147369, d169885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147369, d169885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147370 q = 1) (hb : d169886 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147370, d169886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147370, d169886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d147371 q = 1) (hb : d169887 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147371, d169887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147371, d169887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147374 q = 1) (hb : d169890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147374, d169890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37222 q ha hb
    | true =>
      simp only [d147374, d169890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37223 q ha hb
  have h21 (q : Pattern) (ha : d147375 q = 1) (hb : d169891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147375, d169891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147375, d169891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d147376 q = 1) (hb : d169892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147376, d169892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147376, d169892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147378 q = 1) (hb : d169894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147378, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37224 q ha hb
    | true =>
      simp only [d147378, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37206 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147299 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d147379 q = 1) (hb : d169895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d147379, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d147381 q = 1) (hb : d169897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147381, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37225 q ha hb
    | true =>
      simp only [d147381, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d147382 q = 1) (hb : d169898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147382, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d147382, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d147383 q = 1) (hb : d169899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d147383, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d147384 q = 1) (hb : d169900 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147384, d169900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d147384, d169900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d147385 q = 1) (hb : d169901 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147385, d169901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147385, d169901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d147386 q = 1) (hb : d169902 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147386, d169902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147386, d169902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro37227 (p : Pattern) (ha : d147393 p = 1) (hb : d169909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147289 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37203 q ha hb
    | true =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37204 q ha hb
  have h2 (q : Pattern) (ha : d147290 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147290, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147290, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147291 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147291, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147291, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147292 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147292, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147292, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147293 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147293, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147293, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147388 q = 1) (hb : d169904 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147388, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37204 q ha hb
    | true =>
      simp only [d147388, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147389 q = 1) (hb : d169905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147389, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147389, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147390 q = 1) (hb : d169906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147390, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147390, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147391 q = 1) (hb : d169907 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147391, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147391, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147392 q = 1) (hb : d169908 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147392, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147392, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147393 q = 1) (hb : d169909 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147393, d169909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147393, d169909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37228 (p : Pattern) (ha : d147399 p = 1) (hb : d169915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147388 q = 1) (hb : d169904 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147388, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37204 q ha hb
    | true =>
      simp only [d147388, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147389 q = 1) (hb : d169905 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147389, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147389, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147390 q = 1) (hb : d169906 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147390, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147390, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147391 q = 1) (hb : d169907 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147391, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147391, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147392 q = 1) (hb : d169908 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147392, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147392, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147394 q = 1) (hb : d169910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147394, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37207 q ha hb
    | true =>
      simp only [d147394, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147395 q = 1) (hb : d169911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147395, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147395, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147396 q = 1) (hb : d169912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147396, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147396, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147397 q = 1) (hb : d169913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147397, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147397, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147398 q = 1) (hb : d169914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147398, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147398, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147399 q = 1) (hb : d169915 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147399, d169915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147399, d169915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37229 (p : Pattern) (ha : d147406 p = 1) (hb : d169922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147378 q = 1) (hb : d169894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147378, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37224 q ha hb
    | true =>
      simp only [d147378, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37206 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147299 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147379 q = 1) (hb : d169895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147379, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147381 q = 1) (hb : d169897 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147381, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37225 q ha hb
    | true =>
      simp only [d147381, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147382 q = 1) (hb : d169898 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147382, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147382, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147383 q = 1) (hb : d169899 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147383, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147404 q = 1) (hb : d169920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147404, d169920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147404, d169920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147405 q = 1) (hb : d169921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147405, d169921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147405, d169921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147406 q = 1) (hb : d169922 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147406, d169922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147406, d169922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37230 (p : Pattern) (ha : d147408 p = 1) (hb : d169924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147394 q = 1) (hb : d169910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147394, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37207 q ha hb
    | true =>
      simp only [d147394, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147395 q = 1) (hb : d169911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147395, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147395, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147396 q = 1) (hb : d169912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147396, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147396, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147397 q = 1) (hb : d169913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147397, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147397, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147398 q = 1) (hb : d169914 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147398, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147398, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147408 q = 1) (hb : d169924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147408, d169924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147408, d169924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37231 (p : Pattern) (ha : d147424 p = 1) (hb : d169932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21612 q = 1) (hb : d147414 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21612, d147414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21612, d147414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28161 q ha hb
  have h2 (q : Pattern) (ha : d21482 q = 1) (hb : d147326 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21482, d147326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28161 q ha hb
    | true =>
      simp only [d21482, d147326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21613 q = 1) (hb : d147415 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21613, d147415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21613, d147415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21483 q = 1) (hb : d147327 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21483, d147327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21483, d147327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21614 q = 1) (hb : d147416 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21614, d147416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21614, d147416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21615 q = 1) (hb : d147417 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21615, d147417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21615, d147417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d147188 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147418 q = 1) (hb : d169930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147418, d169930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147418, d169930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d21617 q = 1) (hb : d147419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21617, d147419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21617, d147419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37213 q ha hb
  have h10 (q : Pattern) (ha : d21488 q = 1) (hb : d147332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21488, d147332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37213 q ha hb
    | true =>
      simp only [d21488, d147332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21618 q = 1) (hb : d147420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21618, d147420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21618, d147420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21489 q = 1) (hb : d147333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21489, d147333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21489, d147333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21619 q = 1) (hb : d147421 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21619, d147421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21619, d147421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21620 q = 1) (hb : d147422 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21620, d147422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21620, d147422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d147193 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d147423 q = 1) (hb : d169931 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147423, d169931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d147423, d169931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d147424 q = 1) (hb : d169932 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147424, d169932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147424, d169932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro37232 (p : Pattern) (ha : d147426 p = 1) (hb : d169724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21309 q = 1) (hb : d147185 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21309, d147185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21309, d147185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28118 q ha hb
  have h2 (q : Pattern) (ha : d21183 q = 1) (hb : d147097 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28118 q ha hb
    | true =>
      simp only [d21183, d147097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21310 q = 1) (hb : d147186 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21310, d147186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21310, d147186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21184 q = 1) (hb : d147098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21184, d147098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21311 q = 1) (hb : d147187 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21311, d147187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21311, d147187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21312 q = 1) (hb : d147188 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21312, d147188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21312, d147188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d147003 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147189 q = 1) (hb : d169722 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147189, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147189, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d21314 q = 1) (hb : d147190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21314, d147190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21314, d147190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
  have h10 (q : Pattern) (ha : d21189 q = 1) (hb : d147103 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29721 q ha hb
    | true =>
      simp only [d21189, d147103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21315 q = 1) (hb : d147191 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21315, d147191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21315, d147191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21190 q = 1) (hb : d147104 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21190, d147104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21316 q = 1) (hb : d147192 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21316, d147192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21316, d147192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21317 q = 1) (hb : d147193 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21317, d147193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21317, d147193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d147425 q = 1) (hb : d169723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147425, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d147425, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d147426 q = 1) (hb : d169724 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147426, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147426, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro37233 (p : Pattern) (ha : d147430 p = 1) (hb : d169936 p = 1) : d0 p = 1 := by
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
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147425 q = 1) (hb : d169723 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147425, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147425, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h10 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d980 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d147430 q = 1) (hb : d169936 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147430, d169936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147430, d169936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37234 (p : Pattern) (ha : d147435 p = 1) (hb : d169941 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21071 q = 1) (hb : d147000 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21071, d147000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21071, d147000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28086 q ha hb
  have h2 (q : Pattern) (ha : d20990 q = 1) (hb : d146936 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28086 q ha hb
    | true =>
      simp only [d20990, d146936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21072 q = 1) (hb : d147001 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21072, d147001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21072, d147001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20991 q = 1) (hb : d146937 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20991, d146937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21073 q = 1) (hb : d147002 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21073, d147002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21073, d147002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21074 q = 1) (hb : d147003 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21074, d147003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21074, d147003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147004 q = 1) (hb : d169552 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147004, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147004, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d971 q = 1) (hb : d52590 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d52590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
  have h10 (q : Pattern) (ha : d751 q = 1) (hb : d52428 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100 q ha hb
    | true =>
      simp only [d751, d52428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d972 q = 1) (hb : d52591 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d972, d52591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d752 q = 1) (hb : d52429 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d752, d52429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d973 q = 1) (hb : d52592 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d973, d52592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d974 q = 1) (hb : d52593 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d974, d52593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d980 q = 1) (hb : d52599 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d980, d52599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d147435 q = 1) (hb : d169941 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147435, d169941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147435, d169941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37235 (p : Pattern) (ha : d147444 p = 1) (hb : d169950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147427 q = 1) (hb : d169933 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147427, d169933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37231 q ha hb
    | true =>
      simp only [d147427, d169933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37232 q ha hb
  have h2 (q : Pattern) (ha : d147428 q = 1) (hb : d169934 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147428, d169934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147428, d169934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147429 q = 1) (hb : d169935 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147429, d169935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147429, d169935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147431 q = 1) (hb : d169937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147431, d169937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37232 q ha hb
    | true =>
      simp only [d147431, d169937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37233 q ha hb
  have h5 (q : Pattern) (ha : d147432 q = 1) (hb : d169938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147432, d169938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147432, d169938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147433 q = 1) (hb : d169939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147433, d169939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147433, d169939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147434 q = 1) (hb : d169940 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147434, d169940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147434, d169940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147436 q = 1) (hb : d169942 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147436, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37232 q ha hb
    | true =>
      simp only [d147436, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37234 q ha hb
  have h9 (q : Pattern) (ha : d147437 q = 1) (hb : d169943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147437, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147437, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147438 q = 1) (hb : d169944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147438, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147438, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147439 q = 1) (hb : d169945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147439, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37234 q ha hb
    | true =>
      simp only [d147439, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h12 (q : Pattern) (ha : d147440 q = 1) (hb : d169946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147440, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147440, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147441 q = 1) (hb : d169947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147441, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147441, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147442 q = 1) (hb : d169948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147442, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147442, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147443 q = 1) (hb : d169949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147443, d169949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147443, d169949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147444 q = 1) (hb : d169950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147444, d169950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147444, d169950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37236 (p : Pattern) (ha : d147449 p = 1) (hb : d169955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147436 q = 1) (hb : d169942 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147436, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37232 q ha hb
    | true =>
      simp only [d147436, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37234 q ha hb
  have h2 (q : Pattern) (ha : d147437 q = 1) (hb : d169943 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147437, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147437, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147438 q = 1) (hb : d169944 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147438, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147438, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147439 q = 1) (hb : d169945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147439, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37234 q ha hb
    | true =>
      simp only [d147439, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h5 (q : Pattern) (ha : d147440 q = 1) (hb : d169946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147440, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147440, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147441 q = 1) (hb : d169947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147441, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147441, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147442 q = 1) (hb : d169948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147442, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147442, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147447 q = 1) (hb : d169953 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147447, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147447, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147448 q = 1) (hb : d169954 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147448, d169954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147448, d169954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147449 q = 1) (hb : d169955 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147449, d169955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147449, d169955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37237 (p : Pattern) (ha : d147455 p = 1) (hb : d169961 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147445 q = 1) (hb : d169951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147445, d169951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37235 q ha hb
    | true =>
      simp only [d147445, d169951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147446 q = 1) (hb : d169952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147446, d169952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147446, d169952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147450 q = 1) (hb : d169956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147450, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37236 q ha hb
    | true =>
      simp only [d147450, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147451 q = 1) (hb : d169957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147451, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147451, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147452 q = 1) (hb : d169958 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147452, d169958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147452, d169958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147453 q = 1) (hb : d169959 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147453, d169959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147453, d169959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147454 q = 1) (hb : d169960 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147454, d169960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147454, d169960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147455 q = 1) (hb : d169961 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147455, d169961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147455, d169961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37238 (p : Pattern) (ha : d147457 p = 1) (hb : d169963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147439 q = 1) (hb : d169945 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147439, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37234 q ha hb
    | true =>
      simp only [d147439, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro116 q hb ha
  have h2 (q : Pattern) (ha : d147440 q = 1) (hb : d169946 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147440, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147440, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147441 q = 1) (hb : d169947 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147441, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147441, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147447 q = 1) (hb : d169953 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147447, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147447, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147456 q = 1) (hb : d169962 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147456, d169962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147456, d169962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147457 q = 1) (hb : d169963 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147457, d169963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147457, d169963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37239 (p : Pattern) (ha : d147463 p = 1) (hb : d169969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147450 q = 1) (hb : d169956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147450, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37236 q ha hb
    | true =>
      simp only [d147450, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147451 q = 1) (hb : d169957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147451, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147451, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147458 q = 1) (hb : d169964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147458, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37238 q ha hb
    | true =>
      simp only [d147458, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147459 q = 1) (hb : d169965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147459, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147459, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147460 q = 1) (hb : d169966 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147460, d169966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147460, d169966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147461 q = 1) (hb : d169967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147461, d169967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147461, d169967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147462 q = 1) (hb : d169968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147462, d169968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147462, d169968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147463 q = 1) (hb : d169969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147463, d169969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147463, d169969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37240 (p : Pattern) (ha : d147474 p = 1) (hb : d169975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147450 q = 1) (hb : d169956 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147450, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37236 q ha hb
    | true =>
      simp only [d147450, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147451 q = 1) (hb : d169957 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147451, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147451, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147471 q = 1) (hb : d169972 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147471, d169972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147471, d169972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147472 q = 1) (hb : d169973 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147472, d169973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147472, d169973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147473 q = 1) (hb : d169974 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147473, d169974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147473, d169974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147474 q = 1) (hb : d169975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147474, d169975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147474, d169975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37241 (p : Pattern) (ha : d147480 p = 1) (hb : d169981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147464 q = 1) (hb : d169970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147464, d169970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37237 q ha hb
    | true =>
      simp only [d147464, d169970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37239 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147469 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147470 q = 1) (hb : d169971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147470, d169971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147470, d169971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147475 q = 1) (hb : d169976 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147475, d169976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37240 q ha hb
    | true =>
      simp only [d147475, d169976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147476 q = 1) (hb : d169977 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147476, d169977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147476, d169977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147477 q = 1) (hb : d169978 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147477, d169978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147477, d169978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147478 q = 1) (hb : d169979 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147478, d169979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147478, d169979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147479 q = 1) (hb : d169980 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147479, d169980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147479, d169980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147480 q = 1) (hb : d169981 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147480, d169981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147480, d169981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37242 (p : Pattern) (ha : d147468 p = 1) (hb : d169986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147458 q = 1) (hb : d169964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147458, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37238 q ha hb
    | true =>
      simp only [d147458, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147459 q = 1) (hb : d169965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147459, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147459, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147465 q = 1) (hb : d169983 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147465, d169983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147465, d169983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147466 q = 1) (hb : d169984 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147466, d169984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147466, d169984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147467 q = 1) (hb : d169985 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147467, d169985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147467, d169985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147468 q = 1) (hb : d169986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147468, d169986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147468, d169986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37243 (p : Pattern) (ha : d147487 p = 1) (hb : d169992 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147482 q = 1) (hb : d169987 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147482, d169987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37242 q ha hb
    | true =>
      simp only [d147482, d169987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147483 q = 1) (hb : d169988 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147483, d169988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147483, d169988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147484 q = 1) (hb : d169989 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147484, d169989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147484, d169989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147485 q = 1) (hb : d169990 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147485, d169990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147485, d169990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147486 q = 1) (hb : d169991 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147486, d169991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147486, d169991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147487 q = 1) (hb : d169992 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147487, d169992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147487, d169992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37244 (p : Pattern) (ha : d147493 p = 1) (hb : d169998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147295 q = 1) (hb : d169821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147295, d169821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147295, d169821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37205 q ha hb
  have h2 (q : Pattern) (ha : d147296 q = 1) (hb : d169822 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147296, d169822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147296, d169822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147305 q = 1) (hb : d169831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147305, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37205 q ha hb
    | true =>
      simp only [d147305, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37208 q ha hb
  have h4 (q : Pattern) (ha : d147306 q = 1) (hb : d169832 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147306, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147306, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147307 q = 1) (hb : d169833 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147307, d169833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147307, d169833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147387 q = 1) (hb : d169903 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147387, d169903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37219 q ha hb
    | true =>
      simp only [d147387, d169903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37226 q ha hb
  have h7 (q : Pattern) (ha : d147400 q = 1) (hb : d169916 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147400, d169916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37227 q ha hb
    | true =>
      simp only [d147400, d169916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37228 q ha hb
  have h8 (q : Pattern) (ha : d147401 q = 1) (hb : d169917 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147401, d169917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147401, d169917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147402 q = 1) (hb : d169918 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147402, d169918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147402, d169918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d147403 q = 1) (hb : d169919 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147403, d169919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147403, d169919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147407 q = 1) (hb : d169923 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147407, d169923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147407, d169923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37229 q ha hb
  have h12 (q : Pattern) (ha : d147409 q = 1) (hb : d169925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147409, d169925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147409, d169925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37230 q ha hb
  have h13 (q : Pattern) (ha : d147410 q = 1) (hb : d169926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147410, d169926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147410, d169926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147411 q = 1) (hb : d169927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147411, d169927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147411, d169927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d147412 q = 1) (hb : d169928 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147412, d169928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d147412, d169928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d147413 q = 1) (hb : d169929 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147413, d169929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147413, d169929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147481 q = 1) (hb : d169982 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147481, d169982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147481, d169982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37241 q ha hb
  have h18 (q : Pattern) (ha : d147488 q = 1) (hb : d169993 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147488, d169993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147488, d169993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37243 q ha hb
  have h19 (q : Pattern) (ha : d147489 q = 1) (hb : d169994 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147489, d169994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147489, d169994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147490 q = 1) (hb : d169995 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147490, d169995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147490, d169995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147491 q = 1) (hb : d169996 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147491, d169996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147491, d169996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147492 q = 1) (hb : d169997 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147492, d169997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147492, d169997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147493 q = 1) (hb : d169998 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147493, d169998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147493, d169998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37245 (p : Pattern) (ha : d147499 p = 1) (hb : d170004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147494 q = 1) (hb : d169999 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147494, d169999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147494, d169999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37244 q ha hb
  have h2 (q : Pattern) (ha : d147495 q = 1) (hb : d170000 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147495, d170000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147495, d170000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147496 q = 1) (hb : d170001 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147496, d170001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147496, d170001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147497 q = 1) (hb : d170002 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147497, d170002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147497, d170002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147498 q = 1) (hb : d170003 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147498, d170003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147498, d170003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147499 q = 1) (hb : d170004 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147499, d170004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147499, d170004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37246 (p : Pattern) (ha : d21771 p = 1) (hb : d147537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21766 q = 1) (hb : d147532 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29751 q ha hb
    | true =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21767 q = 1) (hb : d147533 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21768 q = 1) (hb : d147534 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21768, d147534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21768, d147534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21769 q = 1) (hb : d147535 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21769, d147535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21769, d147535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21770 q = 1) (hb : d147536 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21770, d147536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21770, d147536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d122941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21771 q = 1) (hb : d147537 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21771, d147537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21771, d147537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37247 (p : Pattern) (ha : d21777 p = 1) (hb : d147543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21755 q = 1) (hb : d147521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
    | true =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21756 q = 1) (hb : d147522 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21757 q = 1) (hb : d147523 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21757, d147523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21757, d147523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21758 q = 1) (hb : d147524 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21758, d147524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21758, d147524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21776 q = 1) (hb : d147542 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21776, d147542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21776, d147542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d122941 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d122941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d122942 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d122942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d122943 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d122943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21777 q = 1) (hb : d147543 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21777, d147543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21777, d147543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37248 (p : Pattern) (ha : d21747 p = 1) (hb : d147513 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1088 q = 1) (hb : d52669 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro74 q ha hb
    | true =>
      simp only [d1088, d52669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1089 q = 1) (hb : d52670 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1089, d52670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9581 q = 1) (hb : d101161 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9581, d101161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9582 q = 1) (hb : d101162 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9582, d101162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d9768 q = 1) (hb : d101289 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d101289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9768, d101289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9769 q = 1) (hb : d101290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d101290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9769, d101290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9770 q = 1) (hb : d101291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d101291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9770, d101291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d21747 q = 1) (hb : d147513 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21747, d147513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21747, d147513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h8 p ha hb
theorem andIntro37249 (p : Pattern) (ha : d147519 p = 1) (hb : d170009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21737 q = 1) (hb : d147503 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d147503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28192 q ha hb
    | true =>
      simp only [d21737, d147503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21738 q = 1) (hb : d147504 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d147504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21738, d147504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21739 q = 1) (hb : d147505 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21739, d147505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21739, d147505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21740 q = 1) (hb : d147506 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21740, d147506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21740, d147506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147511 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147512 q = 1) (hb : d170007 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147512, d170007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147512, d170007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21748 q = 1) (hb : d147514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d147514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37248 q ha hb
    | true =>
      simp only [d21748, d147514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21749 q = 1) (hb : d147515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d147515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21749, d147515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21750 q = 1) (hb : d147516 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21750, d147516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21750, d147516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21751 q = 1) (hb : d147517 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21751, d147517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21751, d147517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147518 q = 1) (hb : d170008 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147518, d170008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147518, d170008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d147519 q = 1) (hb : d170009 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147519, d170009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147519, d170009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
end NetHack.Soko22Hazard87
