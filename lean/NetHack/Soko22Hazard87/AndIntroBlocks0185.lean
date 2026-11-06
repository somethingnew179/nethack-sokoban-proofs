import NetHack.Soko22Hazard87.AndIntroBlocks0184
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro46250 (p : Pattern) (ha : d113704 p = 1) (hb : d149461 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17004 q = 1) (hb : d53183 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d53183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d52996 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46211 q ha hb
    | true =>
      simp only [d10036, d52996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17005 q = 1) (hb : d53184 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17005, d53184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10038 q = 1) (hb : d52997 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d52997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17006 q = 1) (hb : d53185 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17006, d53185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17007 q = 1) (hb : d53186 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17007, d53186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22508 q = 1) (hb : d53188 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d53188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
  have h8 (q : Pattern) (ha : d22220 q = 1) (hb : d53011 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46207 q ha hb
    | true =>
      simp only [d22220, d53011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22509 q = 1) (hb : d53189 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22509, d53189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22221 q = 1) (hb : d53012 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22221, d53012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22510 q = 1) (hb : d53190 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22510, d53190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22511 q = 1) (hb : d53191 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22511, d53191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22512 q = 1) (hb : d53192 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22512, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22512, d53192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113704 q = 1) (hb : d149461 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113704, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d113704, d149461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro46251 (p : Pattern) (ha : d113717 p = 1) (hb : d152264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22518 q = 1) (hb : d113708 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22518, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22518, d113708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46227 q ha hb
  have h2 (q : Pattern) (ha : d22324 q = 1) (hb : d101526 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46227 q ha hb
    | true =>
      simp only [d22324, d101526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22519 q = 1) (hb : d113709 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22519, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22519, d113709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22325 q = 1) (hb : d101528 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22325, d101528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22520 q = 1) (hb : d113710 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22520, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22520, d113710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22521 q = 1) (hb : d113711 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22521, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22521, d113711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13490 q = 1) (hb : d113712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
  have h8 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13491 q = 1) (hb : d113713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13492 q = 1) (hb : d113714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13493 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22522 q = 1) (hb : d113716 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22522, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22522, d113716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113717 q = 1) (hb : d152264 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113717, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d113717, d152264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro46252 (p : Pattern) (ha : d113727 p = 1) (hb : d152278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113705 q = 1) (hb : d152261 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113705, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46249 q ha hb
    | true =>
      simp only [d113705, d152261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46250 q ha hb
  have h2 (q : Pattern) (ha : d113706 q = 1) (hb : d152262 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113706, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113706, d152262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113707 q = 1) (hb : d152263 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113707, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113707, d152263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113718 q = 1) (hb : d152265 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113718, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46250 q ha hb
    | true =>
      simp only [d113718, d152265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46251 q ha hb
  have h5 (q : Pattern) (ha : d113719 q = 1) (hb : d152266 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113719, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113719, d152266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113720 q = 1) (hb : d152267 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113720, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113720, d152267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113721 q = 1) (hb : d152268 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113721, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113721, d152268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113722 q = 1) (hb : d152269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46250 q ha hb
    | true =>
      simp only [d113722, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
  have h9 (q : Pattern) (ha : d113723 q = 1) (hb : d152270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113724 q = 1) (hb : d152271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76231 q = 1) (hb : d152273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
    | true =>
      simp only [d76231, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46248 q ha hb
  have h12 (q : Pattern) (ha : d76232 q = 1) (hb : d152274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76233 q = 1) (hb : d152275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113725 q = 1) (hb : d152276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113725, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113726 q = 1) (hb : d152277 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113726, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113726, d152277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113727 q = 1) (hb : d152278 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113727, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113727, d152278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro46253 (p : Pattern) (ha : d113731 p = 1) (hb : d152283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113722 q = 1) (hb : d152269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46250 q ha hb
    | true =>
      simp only [d113722, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
  have h2 (q : Pattern) (ha : d113723 q = 1) (hb : d152270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113724 q = 1) (hb : d152271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76231 q = 1) (hb : d152273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
    | true =>
      simp only [d76231, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46248 q ha hb
  have h5 (q : Pattern) (ha : d76232 q = 1) (hb : d152274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76233 q = 1) (hb : d152275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113725 q = 1) (hb : d152276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113725, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76234 q = 1) (hb : d152281 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76234, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76234, d152281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113730 q = 1) (hb : d152282 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113730, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113730, d152282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113731 q = 1) (hb : d152283 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113731, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113731, d152283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro46254 (p : Pattern) (ha : d113737 p = 1) (hb : d152289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113728 q = 1) (hb : d152279 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113728, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46252 q ha hb
    | true =>
      simp only [d113728, d152279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113729 q = 1) (hb : d152280 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113729, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113729, d152280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113732 q = 1) (hb : d152284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46253 q ha hb
    | true =>
      simp only [d113732, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113733 q = 1) (hb : d152285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113734 q = 1) (hb : d152286 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113734, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113734, d152286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113735 q = 1) (hb : d152287 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113735, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113735, d152287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113736 q = 1) (hb : d152288 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113736, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113736, d152288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113737 q = 1) (hb : d152289 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113737, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113737, d152289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46255 (p : Pattern) (ha : d22639 p = 1) (hb : d113738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22529 q = 1) (hb : d53194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d53194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
  have h2 (q : Pattern) (ha : d22233 q = 1) (hb : d53023 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46205 q ha hb
    | true =>
      simp only [d22233, d53023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22530 q = 1) (hb : d53195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22530, d53195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22234 q = 1) (hb : d53024 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22234, d53024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22531 q = 1) (hb : d53196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22531, d53196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22532 q = 1) (hb : d53197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22532, d53197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22561 q = 1) (hb : d53203 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22561, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22561, d53203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22639 q = 1) (hb : d113738 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22639, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22639, d113738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46256 (p : Pattern) (ha : d113744 p = 1) (hb : d152295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113739 q = 1) (hb : d152290 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113739, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
    | true =>
      simp only [d113739, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46255 q hb ha
  have h2 (q : Pattern) (ha : d113740 q = 1) (hb : d152291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113740, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113740, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113741 q = 1) (hb : d152292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113741, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113741, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113742 q = 1) (hb : d152293 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113742, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113742, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113743 q = 1) (hb : d152294 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113743, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113743, d152294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113744 q = 1) (hb : d152295 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113744, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113744, d152295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46257 (p : Pattern) (ha : d113750 p = 1) (hb : d152301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113732 q = 1) (hb : d152284 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46253 q ha hb
    | true =>
      simp only [d113732, d152284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113733 q = 1) (hb : d152285 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d152285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113745 q = 1) (hb : d152296 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46256 q ha hb
    | true =>
      simp only [d113745, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113746 q = 1) (hb : d152297 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113747 q = 1) (hb : d152298 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113747, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113747, d152298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113748 q = 1) (hb : d152299 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113748, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113748, d152299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113749 q = 1) (hb : d152300 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113749, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113749, d152300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113750 q = 1) (hb : d152301 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113750, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113750, d152301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46258 (p : Pattern) (ha : d113753 p = 1) (hb : d152305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113722 q = 1) (hb : d152269 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46250 q ha hb
    | true =>
      simp only [d113722, d152269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
  have h2 (q : Pattern) (ha : d113723 q = 1) (hb : d152270 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d152270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113724 q = 1) (hb : d152271 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d152271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76231 q = 1) (hb : d152273 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
    | true =>
      simp only [d76231, d152273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46248 q ha hb
  have h5 (q : Pattern) (ha : d76232 q = 1) (hb : d152274 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d152274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76233 q = 1) (hb : d152275 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d152275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113725 q = 1) (hb : d152276 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113725, d152276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113739 q = 1) (hb : d152290 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113739, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46247 q ha hb
    | true =>
      simp only [d113739, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46255 q hb ha
  have h9 (q : Pattern) (ha : d113740 q = 1) (hb : d152291 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113740, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113740, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113741 q = 1) (hb : d152292 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113741, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113741, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113742 q = 1) (hb : d152293 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113742, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113742, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113752 q = 1) (hb : d152304 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113752, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113752, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113753 q = 1) (hb : d152305 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113753, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113753, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro46259 (p : Pattern) (ha : d113769 p = 1) (hb : d152311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113754 q = 1) (hb : d152306 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113754, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46258 q ha hb
    | true =>
      simp only [d113754, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113755 q = 1) (hb : d152307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113755, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113755, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113766 q = 1) (hb : d152308 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113766, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113766, d152308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113767 q = 1) (hb : d152309 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113767, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113767, d152309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113768 q = 1) (hb : d152310 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113768, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113768, d152310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113769 q = 1) (hb : d152311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113769, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113769, d152311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46260 (p : Pattern) (ha : d113775 p = 1) (hb : d152317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113751 q = 1) (hb : d152302 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113751, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46254 q ha hb
    | true =>
      simp only [d113751, d152302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113765 q = 1) (hb : d152303 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113765, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113765, d152303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113770 q = 1) (hb : d152312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113770, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46259 q ha hb
    | true =>
      simp only [d113770, d152312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113771 q = 1) (hb : d152313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113771, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113771, d152313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113772 q = 1) (hb : d152314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113772, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113772, d152314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113773 q = 1) (hb : d152315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113773, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113773, d152315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113774 q = 1) (hb : d152316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113774, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113774, d152316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113775 q = 1) (hb : d152317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113775, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113775, d152317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46261 (p : Pattern) (ha : d113763 p = 1) (hb : d152322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113745 q = 1) (hb : d152296 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46256 q ha hb
    | true =>
      simp only [d113745, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113746 q = 1) (hb : d152297 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113760 q = 1) (hb : d152319 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113760, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113760, d152319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113761 q = 1) (hb : d152320 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113761, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113761, d152320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113762 q = 1) (hb : d152321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113762, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113762, d152321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113763 q = 1) (hb : d152322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113763, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113763, d152322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46262 (p : Pattern) (ha : d113782 p = 1) (hb : d152328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113777 q = 1) (hb : d152323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113777, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46261 q ha hb
    | true =>
      simp only [d113777, d152323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113778 q = 1) (hb : d152324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113778, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113778, d152324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113779 q = 1) (hb : d152325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113779, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113779, d152325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113780 q = 1) (hb : d152326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113780, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113780, d152326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113781 q = 1) (hb : d152327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113781, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113781, d152327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113782 q = 1) (hb : d152328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113782, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113782, d152328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46263 (p : Pattern) (ha : d113788 p = 1) (hb : d152334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113574 q = 1) (hb : d152140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113574, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113574, d152140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46217 q ha hb
  have h2 (q : Pattern) (ha : d113575 q = 1) (hb : d152141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113575, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113575, d152141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113584 q = 1) (hb : d152150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113584, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46217 q ha hb
    | true =>
      simp only [d113584, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46220 q ha hb
  have h4 (q : Pattern) (ha : d113585 q = 1) (hb : d152151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113585, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113585, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113586 q = 1) (hb : d152152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113586, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113586, d152152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113671 q = 1) (hb : d152229 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113671, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46234 q ha hb
    | true =>
      simp only [d113671, d152229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46242 q ha hb
  have h7 (q : Pattern) (ha : d113689 q = 1) (hb : d152247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113689, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46243 q ha hb
    | true =>
      simp only [d113689, d152247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46244 q ha hb
  have h8 (q : Pattern) (ha : d113690 q = 1) (hb : d152248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113690, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113690, d152248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113691 q = 1) (hb : d152249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113691, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113691, d152249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113692 q = 1) (hb : d152250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113692, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113692, d152250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113696 q = 1) (hb : d152254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113696, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113696, d152254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46245 q ha hb
  have h12 (q : Pattern) (ha : d113698 q = 1) (hb : d152256 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113698, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113698, d152256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46246 q ha hb
  have h13 (q : Pattern) (ha : d113699 q = 1) (hb : d152257 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113699, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113699, d152257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113700 q = 1) (hb : d152258 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113700, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113700, d152258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113701 q = 1) (hb : d152259 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113701, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113701, d152259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113702 q = 1) (hb : d152260 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113702, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113702, d152260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113776 q = 1) (hb : d152318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113776, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113776, d152318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46260 q ha hb
  have h18 (q : Pattern) (ha : d113783 q = 1) (hb : d152329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113783, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113783, d152329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46262 q ha hb
  have h19 (q : Pattern) (ha : d113784 q = 1) (hb : d152330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113784, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113784, d152330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113785 q = 1) (hb : d152331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113785, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113785, d152331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113786 q = 1) (hb : d152332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113786, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113786, d152332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113787 q = 1) (hb : d152333 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113787, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113787, d152333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113788 q = 1) (hb : d152334 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113788, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113788, d152334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46264 (p : Pattern) (ha : d113794 p = 1) (hb : d152340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113789 q = 1) (hb : d152335 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113789, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113789, d152335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46263 q ha hb
  have h2 (q : Pattern) (ha : d113790 q = 1) (hb : d152336 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113790, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113790, d152336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113791 q = 1) (hb : d152337 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113791, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113791, d152337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113792 q = 1) (hb : d152338 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113792, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113792, d152338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113793 q = 1) (hb : d152339 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113793, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113793, d152339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113794 q = 1) (hb : d152340 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113794, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113794, d152340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46265 (p : Pattern) (ha : d22687 p = 1) (hb : d53343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2041 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro263 q ha hb
    | true =>
      simp only [d2041, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h5 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h6 (q : Pattern) (ha : d2044 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2044, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2045 q = 1) (hb : d53324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2045, d53324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2050 q = 1) (hb : d53329 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2050, d53329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2051 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2051, d53330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d53342 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d22687 q = 1) (hb : d53343 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22687, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22687, d53343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro46266 (p : Pattern) (ha : d22854 p = 1) (hb : d113804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22690 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22691 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22709 q = 1) (hb : d53350 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22709, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22709, d53350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22854 q = 1) (hb : d113804 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22854, d113804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22854, d113804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46267 (p : Pattern) (ha : d10363 p = 1) (hb : d53331 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h5 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h6 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2026 q = 1) (hb : d53305 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2026, d53305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2031 q = 1) (hb : d53310 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2031, d53310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2032 q = 1) (hb : d53311 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2032, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2032, d53311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2033 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2033, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2033, d53312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d53330 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d10363 q = 1) (hb : d53331 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10363, d53331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10363, d53331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro46268 (p : Pattern) (ha : d69321 p = 1) (hb : d149535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17153 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17154 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22690 q = 1) (hb : d53346 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d53346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22691 q = 1) (hb : d53347 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22691, d53347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22692 q = 1) (hb : d53348 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22692, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22692, d53348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69321 q = 1) (hb : d149535 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d69321, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d69321, d149535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro46269 (p : Pattern) (ha : d22698 p = 1) (hb : d69330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h3 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h5 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d5240 q = 1) (hb : d69324 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5240, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5240, d69324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d2049 q = 1) (hb : d53328 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2049, d53328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d5241 q = 1) (hb : d69325 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5241, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d5241, d69325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5242 q = 1) (hb : d69326 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5242, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5242, d69326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69329 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22698 q = 1) (hb : d69330 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22698, d69330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22698, d69330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46270 (p : Pattern) (ha : d69336 p = 1) (hb : d152348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22699 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46269 q ha hb
    | true =>
      simp only [d22699, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22700 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22700, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22701 q = 1) (hb : d69333 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22701, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22701, d69333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22702 q = 1) (hb : d69334 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22702, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22702, d69334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22703 q = 1) (hb : d69335 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22703, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22703, d69335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d69336 q = 1) (hb : d152348 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d69336, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d69336, d152348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46271 (p : Pattern) (ha : d10342 p = 1) (hb : d53313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h2 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h3 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d2010 q = 1) (hb : d53289 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2010, d53289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2011 q = 1) (hb : d53290 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2011, d53290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2012 q = 1) (hb : d53291 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2012, d53291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53312 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d10342 q = 1) (hb : d53313 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10342, d53313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10342, d53313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46272 (p : Pattern) (ha : d113799 p = 1) (hb : d149531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17153 q = 1) (hb : d53334 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d53334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17154 q = 1) (hb : d53335 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17154, d53335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22685 q = 1) (hb : d53336 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22685, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22685, d53336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113799 q = 1) (hb : d149531 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113799, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113799, d149531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro46273 (p : Pattern) (ha : d113810 p = 1) (hb : d152358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113800 q = 1) (hb : d152345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46272 q ha hb
    | true =>
      simp only [d113800, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
  have h2 (q : Pattern) (ha : d113801 q = 1) (hb : d152346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113802 q = 1) (hb : d152347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69337 q = 1) (hb : d152349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
    | true =>
      simp only [d69337, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46270 q ha hb
  have h5 (q : Pattern) (ha : d69338 q = 1) (hb : d152350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69339 q = 1) (hb : d152351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113803 q = 1) (hb : d152352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113803, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113805 q = 1) (hb : d152353 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113805, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
    | true =>
      simp only [d113805, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46266 q hb ha
  have h9 (q : Pattern) (ha : d113806 q = 1) (hb : d152354 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113806, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113806, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113807 q = 1) (hb : d152355 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113807, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113807, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113808 q = 1) (hb : d152356 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113808, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113808, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113809 q = 1) (hb : d152357 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113809, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113809, d152357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113810 q = 1) (hb : d152358 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113810, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113810, d152358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro46274 (p : Pattern) (ha : d113814 p = 1) (hb : d152362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113805 q = 1) (hb : d152353 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113805, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
    | true =>
      simp only [d113805, d152353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46266 q hb ha
  have h2 (q : Pattern) (ha : d113806 q = 1) (hb : d152354 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113806, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113806, d152354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113807 q = 1) (hb : d152355 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113807, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113807, d152355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113808 q = 1) (hb : d152356 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113808, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113808, d152356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113813 q = 1) (hb : d152361 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113813, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113813, d152361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113814 q = 1) (hb : d152362 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113814, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113814, d152362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46275 (p : Pattern) (ha : d113820 p = 1) (hb : d152368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d152367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113820 q = 1) (hb : d152368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113820, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113820, d152368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46276 (p : Pattern) (ha : d113824 p = 1) (hb : d152372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113823 q = 1) (hb : d152371 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113823, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113823, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113824 q = 1) (hb : d152372 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113824, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113824, d152372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46277 (p : Pattern) (ha : d113830 p = 1) (hb : d152378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46275 q ha hb
    | true =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46276 q ha hb
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113830 q = 1) (hb : d152378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113830, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113830, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46278 (p : Pattern) (ha : d113833 p = 1) (hb : d152381 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d152367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d152367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113833 q = 1) (hb : d152381 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113833, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113833, d152381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46279 (p : Pattern) (ha : d113834 p = 1) (hb : d152382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113823 q = 1) (hb : d152371 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113823, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113823, d152371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113834 q = 1) (hb : d152382 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113834, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113834, d152382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46280 (p : Pattern) (ha : d113840 p = 1) (hb : d152388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46275 q ha hb
    | true =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46276 q ha hb
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113835 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46278 q ha hb
    | true =>
      simp only [d113835, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46279 q ha hb
  have h7 (q : Pattern) (ha : d113836 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113836, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113836, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113837 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113837, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113837, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113838 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113838, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113838, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113839 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113839, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113839, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113840 q = 1) (hb : d152388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113840, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113840, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46281 (p : Pattern) (ha : d113845 p = 1) (hb : d152393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113844 q = 1) (hb : d152392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113844, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113844, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113845 q = 1) (hb : d152393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113845, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113845, d152393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46282 (p : Pattern) (ha : d113847 p = 1) (hb : d152395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113846 q = 1) (hb : d152394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113846, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113846, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113847 q = 1) (hb : d152395 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113847, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113847, d152395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46283 (p : Pattern) (ha : d113854 p = 1) (hb : d152402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113852 q = 1) (hb : d152400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113852, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113852, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113853 q = 1) (hb : d152401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113853, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113853, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113854 q = 1) (hb : d152402 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113854, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113854, d152402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46284 (p : Pattern) (ha : d113857 p = 1) (hb : d152405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113855 q = 1) (hb : d152403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113855, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113855, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113856 q = 1) (hb : d152404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113856, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113856, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113857 q = 1) (hb : d152405 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113857, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113857, d152405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46285 (p : Pattern) (ha : d13683 p = 1) (hb : d113873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13680 q = 1) (hb : d113870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d13681 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13682 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d13682, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13683 q = 1) (hb : d113873 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13683, d113873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13683, d113873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro46286 (p : Pattern) (ha : d113861 p = 1) (hb : d149593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53426 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17225 q = 1) (hb : d53316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17225, d53316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d17226 q = 1) (hb : d53317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17226, d53317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d22767 q = 1) (hb : d53427 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22767, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22767, d53427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113861 q = 1) (hb : d149593 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113861, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d113861, d149593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro46287 (p : Pattern) (ha : d113879 p = 1) (hb : d152417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113862 q = 1) (hb : d152409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113862, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46286 q ha hb
    | true =>
      simp only [d113862, d152409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46272 q ha hb
  have h2 (q : Pattern) (ha : d113863 q = 1) (hb : d152410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113863, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113863, d152410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113864 q = 1) (hb : d152411 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113864, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113864, d152411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113874 q = 1) (hb : d152412 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113874, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46272 q ha hb
    | true =>
      simp only [d113874, d152412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46285 q hb ha
  have h5 (q : Pattern) (ha : d113875 q = 1) (hb : d152413 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113875, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113875, d152413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113876 q = 1) (hb : d152414 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113876, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113876, d152414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113877 q = 1) (hb : d152415 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113877, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113877, d152415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113800 q = 1) (hb : d152345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46272 q ha hb
    | true =>
      simp only [d113800, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
  have h9 (q : Pattern) (ha : d113801 q = 1) (hb : d152346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113802 q = 1) (hb : d152347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d69337 q = 1) (hb : d152349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
    | true =>
      simp only [d69337, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46270 q ha hb
  have h12 (q : Pattern) (ha : d69338 q = 1) (hb : d152350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d69339 q = 1) (hb : d152351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113803 q = 1) (hb : d152352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113803, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113878 q = 1) (hb : d152416 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113878, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113878, d152416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113879 q = 1) (hb : d152417 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113879, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113879, d152417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro46288 (p : Pattern) (ha : d113883 p = 1) (hb : d152422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113800 q = 1) (hb : d152345 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46272 q ha hb
    | true =>
      simp only [d113800, d152345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
  have h2 (q : Pattern) (ha : d113801 q = 1) (hb : d152346 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d152346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113802 q = 1) (hb : d152347 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d152347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69337 q = 1) (hb : d152349 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46268 q ha hb
    | true =>
      simp only [d69337, d152349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46270 q ha hb
  have h5 (q : Pattern) (ha : d69338 q = 1) (hb : d152350 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d152350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d69339 q = 1) (hb : d152351 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d152351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113803 q = 1) (hb : d152352 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113803, d152352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69340 q = 1) (hb : d152420 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69340, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d69340, d152420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113882 q = 1) (hb : d152421 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113882, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113882, d152421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113883 q = 1) (hb : d152422 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113883, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113883, d152422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro46289 (p : Pattern) (ha : d113889 p = 1) (hb : d152428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113880 q = 1) (hb : d152418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113880, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46287 q ha hb
    | true =>
      simp only [d113880, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113881 q = 1) (hb : d152419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113881, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113881, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113884 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46288 q ha hb
    | true =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113885 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113886 q = 1) (hb : d152425 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113886, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113886, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113887 q = 1) (hb : d152426 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113887, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113887, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113888 q = 1) (hb : d152427 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113888, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113888, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113889 q = 1) (hb : d152428 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113889, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113889, d152428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46290 (p : Pattern) (ha : d113893 p = 1) (hb : d152432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113884 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46288 q ha hb
    | true =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113885 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113890 q = 1) (hb : d152429 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113890, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113890, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113891 q = 1) (hb : d152430 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113891, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113891, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113892 q = 1) (hb : d152431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113892, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113892, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113893 q = 1) (hb : d152432 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113893, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113893, d152432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46291 (p : Pattern) (ha : d113899 p = 1) (hb : d152438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113896 q = 1) (hb : d152435 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113896, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113896, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113897 q = 1) (hb : d152436 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113897, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113897, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113898 q = 1) (hb : d152437 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113898, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113898, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113899 q = 1) (hb : d152438 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113899, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113899, d152438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46292 (p : Pattern) (ha : d113905 p = 1) (hb : d152444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113848 q = 1) (hb : d152396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113848, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46281 q ha hb
    | true =>
      simp only [d113848, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46282 q ha hb
  have h2 (q : Pattern) (ha : d113849 q = 1) (hb : d152397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113849, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113849, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113850 q = 1) (hb : d152398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113850, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113850, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113851 q = 1) (hb : d152399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113851, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113851, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113858 q = 1) (hb : d152406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113858, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46283 q ha hb
    | true =>
      simp only [d113858, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46284 q ha hb
  have h6 (q : Pattern) (ha : d113859 q = 1) (hb : d152407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113859, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113859, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113860 q = 1) (hb : d152408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113860, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113860, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113894 q = 1) (hb : d152433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113894, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46289 q ha hb
    | true =>
      simp only [d113894, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46290 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113825 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113895 q = 1) (hb : d152434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113895, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113900 q = 1) (hb : d152439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113900, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46291 q ha hb
    | true =>
      simp only [d113900, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113901 q = 1) (hb : d152440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113901, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113901, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113902 q = 1) (hb : d152441 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113902, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113903 q = 1) (hb : d152442 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113903, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113904 q = 1) (hb : d152443 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113904, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113905 q = 1) (hb : d152444 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113905, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113905, d152444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro46293 (p : Pattern) (ha : d113906 p = 1) (hb : d152445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d152366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d152366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113844 q = 1) (hb : d152392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113844, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113844, d152392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113906 q = 1) (hb : d152445 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113906, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113906, d152445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46294 (p : Pattern) (ha : d113907 p = 1) (hb : d152446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d152370 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d152370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113846 q = 1) (hb : d152394 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113846, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113846, d152394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113907 q = 1) (hb : d152446 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113907, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113907, d152446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46295 (p : Pattern) (ha : d113912 p = 1) (hb : d152451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d152365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d152365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113852 q = 1) (hb : d152400 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113852, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113852, d152400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113853 q = 1) (hb : d152401 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113853, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113853, d152401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113912 q = 1) (hb : d152451 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113912, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113912, d152451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46296 (p : Pattern) (ha : d113913 p = 1) (hb : d152452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d152369 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d152369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113855 q = 1) (hb : d152403 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113855, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113855, d152403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113856 q = 1) (hb : d152404 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113856, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113856, d152404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113913 q = 1) (hb : d152452 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113913, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113913, d152452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46297 (p : Pattern) (ha : d113917 p = 1) (hb : d152456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113880 q = 1) (hb : d152418 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113880, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46287 q ha hb
    | true =>
      simp only [d113880, d152418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113881 q = 1) (hb : d152419 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113881, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113881, d152419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113884 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46288 q ha hb
    | true =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113885 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113886 q = 1) (hb : d152425 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113886, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113886, d152425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113887 q = 1) (hb : d152426 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113887, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113887, d152426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113888 q = 1) (hb : d152427 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113888, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113888, d152427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113917 q = 1) (hb : d152456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113917, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113917, d152456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46298 (p : Pattern) (ha : d113918 p = 1) (hb : d152457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113884 q = 1) (hb : d152423 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46288 q ha hb
    | true =>
      simp only [d113884, d152423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113885 q = 1) (hb : d152424 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d152424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d152363 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46274 q ha hb
    | true =>
      simp only [d113815, d152363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d152364 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d152364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113890 q = 1) (hb : d152429 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113890, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113890, d152429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113891 q = 1) (hb : d152430 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113891, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113891, d152430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113892 q = 1) (hb : d152431 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113892, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113892, d152431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113918 q = 1) (hb : d152457 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113918, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113918, d152457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46299 (p : Pattern) (ha : d113921 p = 1) (hb : d152460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d152359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46273 q ha hb
    | true =>
      simp only [d113811, d152359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d152360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d152360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113896 q = 1) (hb : d152435 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113896, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113896, d152435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113897 q = 1) (hb : d152436 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113897, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113897, d152436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113898 q = 1) (hb : d152437 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113898, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113898, d152437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113921 q = 1) (hb : d152460 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113921, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113921, d152460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46300 (p : Pattern) (ha : d113927 p = 1) (hb : d152466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113848 q = 1) (hb : d152396 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113848, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46281 q ha hb
    | true =>
      simp only [d113848, d152396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46282 q ha hb
  have h2 (q : Pattern) (ha : d113849 q = 1) (hb : d152397 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113849, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113849, d152397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113850 q = 1) (hb : d152398 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113850, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113850, d152398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113851 q = 1) (hb : d152399 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113851, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113851, d152399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113858 q = 1) (hb : d152406 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113858, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46283 q ha hb
    | true =>
      simp only [d113858, d152406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46284 q ha hb
  have h6 (q : Pattern) (ha : d113859 q = 1) (hb : d152407 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113859, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113859, d152407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113860 q = 1) (hb : d152408 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113860, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113860, d152408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113894 q = 1) (hb : d152433 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113894, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46289 q ha hb
    | true =>
      simp only [d113894, d152433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46290 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113825 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113895 q = 1) (hb : d152434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113895, d152434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113900 q = 1) (hb : d152439 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113900, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46291 q ha hb
    | true =>
      simp only [d113900, d152439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113901 q = 1) (hb : d152440 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113901, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113901, d152440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113902 q = 1) (hb : d152441 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113902, d152441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113903 q = 1) (hb : d152442 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113903, d152442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113904 q = 1) (hb : d152443 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113904, d152443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113908 q = 1) (hb : d152447 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113908, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46293 q ha hb
    | true =>
      simp only [d113908, d152447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46294 q ha hb
  have h17 (q : Pattern) (ha : d113909 q = 1) (hb : d152448 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113909, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113909, d152448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113910 q = 1) (hb : d152449 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113910, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113910, d152449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113911 q = 1) (hb : d152450 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113911, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113911, d152450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113914 q = 1) (hb : d152453 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113914, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46295 q ha hb
    | true =>
      simp only [d113914, d152453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46296 q ha hb
  have h21 (q : Pattern) (ha : d113915 q = 1) (hb : d152454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113915, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113915, d152454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113916 q = 1) (hb : d152455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113916, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113916, d152455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113919 q = 1) (hb : d152458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113919, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46297 q ha hb
    | true =>
      simp only [d113919, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46298 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113835 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113920 q = 1) (hb : d152459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113920, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113922 q = 1) (hb : d152461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113922, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46299 q ha hb
    | true =>
      simp only [d113922, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113923 q = 1) (hb : d152462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113923, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113923, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113924 q = 1) (hb : d152463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113924, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113925 q = 1) (hb : d152464 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113925, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113925, d152464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113926 q = 1) (hb : d152465 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113926, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113926, d152465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113927 q = 1) (hb : d152466 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113927, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113927, d152466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro46301 (p : Pattern) (ha : d113939 p = 1) (hb : d152478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113929 q = 1) (hb : d152468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113929, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46290 q ha hb
    | true =>
      simp only [d113929, d152468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46276 q ha hb
  have h2 (q : Pattern) (ha : d113930 q = 1) (hb : d152469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113930, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113930, d152469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113931 q = 1) (hb : d152470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113931, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113931, d152470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113932 q = 1) (hb : d152471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113932, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113932, d152471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113933 q = 1) (hb : d152472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113933, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113933, d152472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113934 q = 1) (hb : d152473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113934, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46276 q ha hb
    | true =>
      simp only [d113934, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113935 q = 1) (hb : d152474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113935, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113935, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113936 q = 1) (hb : d152475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113936, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113936, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113937 q = 1) (hb : d152476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113937, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113937, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113938 q = 1) (hb : d152477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113938, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113938, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113939 q = 1) (hb : d152478 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113939, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113939, d152478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46302 (p : Pattern) (ha : d113945 p = 1) (hb : d152484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113934 q = 1) (hb : d152473 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113934, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46276 q ha hb
    | true =>
      simp only [d113934, d152473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113935 q = 1) (hb : d152474 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113935, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113935, d152474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113936 q = 1) (hb : d152475 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113936, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113936, d152475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113937 q = 1) (hb : d152476 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113937, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113937, d152476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113938 q = 1) (hb : d152477 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113938, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113938, d152477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113940 q = 1) (hb : d152479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113940, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46279 q ha hb
    | true =>
      simp only [d113940, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113941 q = 1) (hb : d152480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113941, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113941, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113942 q = 1) (hb : d152481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113942, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113942, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113943 q = 1) (hb : d152482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113943, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113943, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113944 q = 1) (hb : d152483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113944, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113944, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113945 q = 1) (hb : d152484 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113945, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113945, d152484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46303 (p : Pattern) (ha : d113952 p = 1) (hb : d152491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113919 q = 1) (hb : d152458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113919, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46297 q ha hb
    | true =>
      simp only [d113919, d152458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46298 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113920 q = 1) (hb : d152459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113920, d152459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113922 q = 1) (hb : d152461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113922, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46299 q ha hb
    | true =>
      simp only [d113922, d152461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113923 q = 1) (hb : d152462 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113923, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113923, d152462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113924 q = 1) (hb : d152463 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113924, d152463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113950 q = 1) (hb : d152489 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113950, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113950, d152489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113951 q = 1) (hb : d152490 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113951, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113951, d152490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113952 q = 1) (hb : d152491 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113952, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113952, d152491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46304 (p : Pattern) (ha : d113954 p = 1) (hb : d152493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113940 q = 1) (hb : d152479 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113940, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46279 q ha hb
    | true =>
      simp only [d113940, d152479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113941 q = 1) (hb : d152480 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113941, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113941, d152480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113942 q = 1) (hb : d152481 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113942, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113942, d152481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113943 q = 1) (hb : d152482 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113943, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113943, d152482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113944 q = 1) (hb : d152483 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113944, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113944, d152483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113954 q = 1) (hb : d152493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113954, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113954, d152493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46305 (p : Pattern) (ha : d13822 p = 1) (hb : d113974 p = 1) : d0 p = 1 := by
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
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13817 q = 1) (hb : d113969 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
  have h8 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13818 q = 1) (hb : d113970 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13819 q = 1) (hb : d113971 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13820 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13821 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13821, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13822 q = 1) (hb : d113974 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d13822, d113974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13822, d113974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro46306 (p : Pattern) (ha : d76360 p = 1) (hb : d149675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17376 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17377 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17378 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17379 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22943 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
  have h8 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22944 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22945 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22946 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22947 q = 1) (hb : d53515 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22947, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22947, d53515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d76360 q = 1) (hb : d149675 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d76360, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d76360, d149675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro46307 (p : Pattern) (ha : d76366 p = 1) (hb : d152509 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22952 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22952, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22952, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46269 q ha hb
  have h2 (q : Pattern) (ha : d22699 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46269 q ha hb
    | true =>
      simp only [d22699, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22953 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22953, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22953, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22700 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22700, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22954 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22954, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22954, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22955 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22955, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22955, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22956 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22956, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22956, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d76366 q = 1) (hb : d152509 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d76366, d152509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d76366, d152509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46308 (p : Pattern) (ha : d113960 p = 1) (hb : d149666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53499 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d17369 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
  have h3 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d17370 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d17371 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17372 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d22930 q = 1) (hb : d53504 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22930, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22930, d53504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113960 q = 1) (hb : d149666 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113960, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d113960, d149666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h9 p ha hb
theorem andIntro46309 (p : Pattern) (ha : d113961 p = 1) (hb : d149670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17369 q = 1) (hb : d53500 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d53500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d53314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46271 q ha hb
    | true =>
      simp only [d10343, d53314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17370 q = 1) (hb : d53501 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17370, d53501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10345 q = 1) (hb : d53315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d53315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17371 q = 1) (hb : d53502 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17371, d53502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17372 q = 1) (hb : d53503 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17372, d53503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d17376 q = 1) (hb : d53505 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d53505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
  have h8 (q : Pattern) (ha : d10364 q = 1) (hb : d53332 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46267 q ha hb
    | true =>
      simp only [d10364, d53332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17377 q = 1) (hb : d53506 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17377, d53506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10366 q = 1) (hb : d53333 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10366, d53333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d17378 q = 1) (hb : d53507 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d17378, d53507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d17379 q = 1) (hb : d53508 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d17379, d53508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22932 q = 1) (hb : d53509 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22932, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22932, d53509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113961 q = 1) (hb : d149670 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d113961, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d113961, d149670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro46310 (p : Pattern) (ha : d113984 p = 1) (hb : d152515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113962 q = 1) (hb : d152499 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113962, d152499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46308 q ha hb
    | true =>
      simp only [d113962, d152499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46309 q ha hb
  have h2 (q : Pattern) (ha : d113963 q = 1) (hb : d152500 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113963, d152500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113963, d152500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113964 q = 1) (hb : d152501 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113964, d152501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113964, d152501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113975 q = 1) (hb : d152502 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113975, d152502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46309 q ha hb
    | true =>
      simp only [d113975, d152502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46305 q hb ha
  have h5 (q : Pattern) (ha : d113976 q = 1) (hb : d152503 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113976, d152503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113976, d152503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113977 q = 1) (hb : d152504 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113977, d152504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113977, d152504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113978 q = 1) (hb : d152505 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113978, d152505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113978, d152505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113979 q = 1) (hb : d152506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46309 q ha hb
    | true =>
      simp only [d113979, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
  have h9 (q : Pattern) (ha : d113980 q = 1) (hb : d152507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113981 q = 1) (hb : d152508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d76367 q = 1) (hb : d152510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
    | true =>
      simp only [d76367, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46307 q ha hb
  have h12 (q : Pattern) (ha : d76368 q = 1) (hb : d152511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d76369 q = 1) (hb : d152512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113982 q = 1) (hb : d152513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113982, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113983 q = 1) (hb : d152514 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113983, d152514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113983, d152514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113984 q = 1) (hb : d152515 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113984, d152515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113984, d152515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro46311 (p : Pattern) (ha : d113988 p = 1) (hb : d152520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113979 q = 1) (hb : d152506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46309 q ha hb
    | true =>
      simp only [d113979, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
  have h2 (q : Pattern) (ha : d113980 q = 1) (hb : d152507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113981 q = 1) (hb : d152508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76367 q = 1) (hb : d152510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
    | true =>
      simp only [d76367, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46307 q ha hb
  have h5 (q : Pattern) (ha : d76368 q = 1) (hb : d152511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76369 q = 1) (hb : d152512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113982 q = 1) (hb : d152513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113982, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76370 q = 1) (hb : d152518 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76370, d152518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d76370, d152518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113987 q = 1) (hb : d152519 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113987, d152519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113987, d152519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113988 q = 1) (hb : d152520 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113988, d152520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113988, d152520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro46312 (p : Pattern) (ha : d113994 p = 1) (hb : d152526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113985 q = 1) (hb : d152516 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113985, d152516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46310 q ha hb
    | true =>
      simp only [d113985, d152516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113986 q = 1) (hb : d152517 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113986, d152517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113986, d152517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113989 q = 1) (hb : d152521 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113989, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46311 q ha hb
    | true =>
      simp only [d113989, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113990 q = 1) (hb : d152522 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113990, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113990, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113991 q = 1) (hb : d152523 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113991, d152523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113991, d152523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113992 q = 1) (hb : d152524 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113992, d152524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113992, d152524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113993 q = 1) (hb : d152525 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113993, d152525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113993, d152525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113994 q = 1) (hb : d152526 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113994, d152526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113994, d152526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46313 (p : Pattern) (ha : d23045 p = 1) (hb : d113995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22943 q = 1) (hb : d53511 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d53511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
  have h2 (q : Pattern) (ha : d22688 q = 1) (hb : d53344 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46265 q ha hb
    | true =>
      simp only [d22688, d53344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22944 q = 1) (hb : d53512 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22944, d53512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22689 q = 1) (hb : d53345 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22689, d53345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22945 q = 1) (hb : d53513 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22945, d53513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22946 q = 1) (hb : d53514 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22946, d53514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22975 q = 1) (hb : d53520 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22975, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22975, d53520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d23045 q = 1) (hb : d113995 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d23045, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23045, d113995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46314 (p : Pattern) (ha : d114001 p = 1) (hb : d152532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113996 q = 1) (hb : d152527 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113996, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
    | true =>
      simp only [d113996, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46313 q hb ha
  have h2 (q : Pattern) (ha : d113997 q = 1) (hb : d152528 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113997, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113997, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113998 q = 1) (hb : d152529 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113998, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113998, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113999 q = 1) (hb : d152530 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113999, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113999, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114000 q = 1) (hb : d152531 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d114000, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114000, d152531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114001 q = 1) (hb : d152532 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d114001, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114001, d152532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46315 (p : Pattern) (ha : d114007 p = 1) (hb : d152538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113989 q = 1) (hb : d152521 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113989, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46311 q ha hb
    | true =>
      simp only [d113989, d152521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113990 q = 1) (hb : d152522 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113990, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113990, d152522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114002 q = 1) (hb : d152533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46314 q ha hb
    | true =>
      simp only [d114002, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114003 q = 1) (hb : d152534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114004 q = 1) (hb : d152535 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114004, d152535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114004, d152535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114005 q = 1) (hb : d152536 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114005, d152536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114005, d152536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d114006 q = 1) (hb : d152537 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114006, d152537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d114006, d152537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d114007 q = 1) (hb : d152538 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114007, d152538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114007, d152538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46316 (p : Pattern) (ha : d114010 p = 1) (hb : d152542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113979 q = 1) (hb : d152506 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46309 q ha hb
    | true =>
      simp only [d113979, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
  have h2 (q : Pattern) (ha : d113980 q = 1) (hb : d152507 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113981 q = 1) (hb : d152508 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76367 q = 1) (hb : d152510 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
    | true =>
      simp only [d76367, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46307 q ha hb
  have h5 (q : Pattern) (ha : d76368 q = 1) (hb : d152511 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d76369 q = 1) (hb : d152512 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113982 q = 1) (hb : d152513 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113982, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113996 q = 1) (hb : d152527 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113996, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46306 q ha hb
    | true =>
      simp only [d113996, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46313 q hb ha
  have h9 (q : Pattern) (ha : d113997 q = 1) (hb : d152528 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113997, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113997, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113998 q = 1) (hb : d152529 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113998, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113998, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113999 q = 1) (hb : d152530 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113999, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113999, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d114009 q = 1) (hb : d152541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d114009, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114009, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114010 q = 1) (hb : d152542 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d114010, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d114010, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro46317 (p : Pattern) (ha : d114026 p = 1) (hb : d152548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114011 q = 1) (hb : d152543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114011, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46316 q ha hb
    | true =>
      simp only [d114011, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114012 q = 1) (hb : d152544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114012, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114012, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114023 q = 1) (hb : d152545 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114023, d152545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114023, d152545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114024 q = 1) (hb : d152546 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114024, d152546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114024, d152546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114025 q = 1) (hb : d152547 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114025, d152547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114025, d152547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114026 q = 1) (hb : d152548 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114026, d152548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114026, d152548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46318 (p : Pattern) (ha : d114032 p = 1) (hb : d152554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114008 q = 1) (hb : d152539 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114008, d152539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46312 q ha hb
    | true =>
      simp only [d114008, d152539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46315 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114021 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d114022 q = 1) (hb : d152540 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114022, d152540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114022, d152540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d114027 q = 1) (hb : d152549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114027, d152549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46317 q ha hb
    | true =>
      simp only [d114027, d152549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114028 q = 1) (hb : d152550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114028, d152550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114028, d152550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114029 q = 1) (hb : d152551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114029, d152551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114029, d152551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d114030 q = 1) (hb : d152552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114030, d152552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114030, d152552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d114031 q = 1) (hb : d152553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114031, d152553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114031, d152553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d114032 q = 1) (hb : d152554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114032, d152554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114032, d152554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro46319 (p : Pattern) (ha : d114020 p = 1) (hb : d152559 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114002 q = 1) (hb : d152533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46314 q ha hb
    | true =>
      simp only [d114002, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114003 q = 1) (hb : d152534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114017 q = 1) (hb : d152556 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114017, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114017, d152556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114018 q = 1) (hb : d152557 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114018, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114018, d152557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114019 q = 1) (hb : d152558 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114019, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114019, d152558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114020 q = 1) (hb : d152559 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114020, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114020, d152559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46320 (p : Pattern) (ha : d114039 p = 1) (hb : d152565 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114034 q = 1) (hb : d152560 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114034, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46319 q ha hb
    | true =>
      simp only [d114034, d152560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114035 q = 1) (hb : d152561 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114035, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114035, d152561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114036 q = 1) (hb : d152562 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114036, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114036, d152562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114037 q = 1) (hb : d152563 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114037, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114037, d152563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114038 q = 1) (hb : d152564 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114038, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114038, d152564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114039 q = 1) (hb : d152565 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114039, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114039, d152565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46321 (p : Pattern) (ha : d114045 p = 1) (hb : d152571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113831 q = 1) (hb : d152379 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113831, d152379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113831, d152379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46277 q ha hb
  have h2 (q : Pattern) (ha : d113832 q = 1) (hb : d152380 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113832, d152380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113832, d152380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113841 q = 1) (hb : d152389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113841, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46277 q ha hb
    | true =>
      simp only [d113841, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46280 q ha hb
  have h4 (q : Pattern) (ha : d113842 q = 1) (hb : d152390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113842, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113842, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113843 q = 1) (hb : d152391 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113843, d152391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113843, d152391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113928 q = 1) (hb : d152467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113928, d152467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46292 q ha hb
    | true =>
      simp only [d113928, d152467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46300 q ha hb
  have h7 (q : Pattern) (ha : d113946 q = 1) (hb : d152485 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113946, d152485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46301 q ha hb
    | true =>
      simp only [d113946, d152485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46302 q ha hb
  have h8 (q : Pattern) (ha : d113947 q = 1) (hb : d152486 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113947, d152486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113947, d152486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113948 q = 1) (hb : d152487 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113948, d152487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113948, d152487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113949 q = 1) (hb : d152488 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113949, d152488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113949, d152488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113953 q = 1) (hb : d152492 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113953, d152492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113953, d152492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46303 q ha hb
  have h12 (q : Pattern) (ha : d113955 q = 1) (hb : d152494 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113955, d152494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113955, d152494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46304 q ha hb
  have h13 (q : Pattern) (ha : d113956 q = 1) (hb : d152495 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113956, d152495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113956, d152495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113957 q = 1) (hb : d152496 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113957, d152496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113957, d152496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113958 q = 1) (hb : d152497 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113958, d152497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113958, d152497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113959 q = 1) (hb : d152498 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113959, d152498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113959, d152498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d114033 q = 1) (hb : d152555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114033, d152555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114033, d152555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46318 q ha hb
  have h18 (q : Pattern) (ha : d114040 q = 1) (hb : d152566 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114040, d152566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114040, d152566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46320 q ha hb
  have h19 (q : Pattern) (ha : d114041 q = 1) (hb : d152567 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d114041, d152567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d114041, d152567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d114042 q = 1) (hb : d152568 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114042, d152568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d114042, d152568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d114043 q = 1) (hb : d152569 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d114043, d152569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d114043, d152569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d114044 q = 1) (hb : d152570 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d114044, d152570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d114044, d152570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d114045 q = 1) (hb : d152571 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d114045, d152571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d114045, d152571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46322 (p : Pattern) (ha : d114051 p = 1) (hb : d152577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114046 q = 1) (hb : d152572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d114046, d152572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114046, d152572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46321 q ha hb
  have h2 (q : Pattern) (ha : d114047 q = 1) (hb : d152573 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d114047, d152573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114047, d152573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114048 q = 1) (hb : d152574 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d114048, d152574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114048, d152574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d114049 q = 1) (hb : d152575 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d114049, d152575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114049, d152575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114050 q = 1) (hb : d152576 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d114050, d152576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114050, d152576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114051 q = 1) (hb : d152577 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d114051, d152577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114051, d152577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46323 (p : Pattern) (ha : d114057 p = 1) (hb : d152583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d113073 q = 1) (hb : d151664 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113073, d151664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46055 q ha hb
    | true =>
      simp only [d113073, d151664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46099 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113284 q = 1) (hb : d151866 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113284, d151866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113284, d151866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46145 q ha hb
  have h3 (q : Pattern) (ha : d113285 q = 1) (hb : d151867 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113285, d151867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d113285, d151867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113539 q = 1) (hb : d152103 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113539, d152103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113539, d152103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46204 q ha hb
  have h5 (q : Pattern) (ha : d113540 q = 1) (hb : d152104 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113540, d152104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113540, d152104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113541 q = 1) (hb : d152105 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113541, d152105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113541, d152105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113795 q = 1) (hb : d152341 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113795, d152341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113795, d152341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46264 q ha hb
  have h8 (q : Pattern) (ha : d113796 q = 1) (hb : d152342 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113796, d152342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113796, d152342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113797 q = 1) (hb : d152343 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113797, d152343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113797, d152343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113798 q = 1) (hb : d152344 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d113798, d152344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113798, d152344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d114052 q = 1) (hb : d152578 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d114052, d152578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114052, d152578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46322 q ha hb
  have h12 (q : Pattern) (ha : d114053 q = 1) (hb : d152579 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d114053, d152579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114053, d152579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114054 q = 1) (hb : d152580 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d114054, d152580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114054, d152580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d114055 q = 1) (hb : d152581 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d114055, d152581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114055, d152581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d114056 q = 1) (hb : d152582 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d114056, d152582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d114056, d152582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d114057 q = 1) (hb : d152583 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d114057, d152583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114057, d152583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro46324 (p : Pattern) (ha : d114063 p = 1) (hb : d152589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114058 q = 1) (hb : d152584 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d114058, d152584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46323 q ha hb
    | true =>
      simp only [d114058, d152584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114059 q = 1) (hb : d152585 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d114059, d152585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114059, d152585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114060 q = 1) (hb : d152586 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d114060, d152586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114060, d152586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114061 q = 1) (hb : d152587 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d114061, d152587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114061, d152587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114062 q = 1) (hb : d152588 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d114062, d152588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114062, d152588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114063 q = 1) (hb : d152589 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d114063, d152589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114063, d152589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46325 (p : Pattern) (ha : d114069 p = 1) (hb : d152595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114064 q = 1) (hb : d152590 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d114064, d152590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46324 q ha hb
    | true =>
      simp only [d114064, d152590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114065 q = 1) (hb : d152591 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d114065, d152591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114065, d152591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114066 q = 1) (hb : d152592 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d114066, d152592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114066, d152592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114067 q = 1) (hb : d152593 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d114067, d152593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114067, d152593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114068 q = 1) (hb : d152594 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d114068, d152594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114068, d152594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114069 q = 1) (hb : d152595 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d114069, d152595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114069, d152595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46326 (p : Pattern) (ha : d114075 p = 1) (hb : d152601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114070 q = 1) (hb : d152596 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d114070, d152596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46325 q ha hb
    | true =>
      simp only [d114070, d152596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114071 q = 1) (hb : d152597 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d114071, d152597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114071, d152597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114072 q = 1) (hb : d152598 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d114072, d152598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114072, d152598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114073 q = 1) (hb : d152599 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d114073, d152599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114073, d152599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114074 q = 1) (hb : d152600 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d114074, d152600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114074, d152600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114075 q = 1) (hb : d152601 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d114075, d152601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114075, d152601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46327 (p : Pattern) (ha : d114081 p = 1) (hb : d152607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114076 q = 1) (hb : d152602 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d114076, d152602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46326 q ha hb
    | true =>
      simp only [d114076, d152602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114077 q = 1) (hb : d152603 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d114077, d152603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114077, d152603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114078 q = 1) (hb : d152604 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d114078, d152604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114078, d152604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114079 q = 1) (hb : d152605 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d114079, d152605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114079, d152605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114080 q = 1) (hb : d152606 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d114080, d152606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114080, d152606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114081 q = 1) (hb : d152607 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d114081, d152607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114081, d152607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46328 (p : Pattern) (ha : d114087 p = 1) (hb : d152613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114082 q = 1) (hb : d152608 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d114082, d152608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46327 q ha hb
    | true =>
      simp only [d114082, d152608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114083 q = 1) (hb : d152609 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d114083, d152609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114083, d152609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114084 q = 1) (hb : d152610 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d114084, d152610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114084, d152610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114085 q = 1) (hb : d152611 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d114085, d152611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114085, d152611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114086 q = 1) (hb : d152612 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d114086, d152612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114086, d152612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114087 q = 1) (hb : d152613 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d114087, d152613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114087, d152613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46329 (p : Pattern) (ha : d114093 p = 1) (hb : d152619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114088 q = 1) (hb : d152614 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d114088, d152614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46328 q ha hb
    | true =>
      simp only [d114088, d152614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114089 q = 1) (hb : d152615 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d114089, d152615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114089, d152615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114090 q = 1) (hb : d152616 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d114090, d152616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114090, d152616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114091 q = 1) (hb : d152617 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d114091, d152617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114091, d152617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114092 q = 1) (hb : d152618 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d114092, d152618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114092, d152618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114093 q = 1) (hb : d152619 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d114093, d152619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114093, d152619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46330 (p : Pattern) (ha : d114099 p = 1) (hb : d152625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114094 q = 1) (hb : d152620 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d114094, d152620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46329 q ha hb
    | true =>
      simp only [d114094, d152620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114095 q = 1) (hb : d152621 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d114095, d152621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114095, d152621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114096 q = 1) (hb : d152622 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d114096, d152622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114096, d152622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114097 q = 1) (hb : d152623 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d114097, d152623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114097, d152623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114098 q = 1) (hb : d152624 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d114098, d152624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114098, d152624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114099 q = 1) (hb : d152625 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d114099, d152625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114099, d152625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46331 (p : Pattern) (ha : d146836 p = 1) (hb : d194340 p = 1) : d152628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d146836 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d146836 q = 1) : d151304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45728 q ha hb
    | true =>
      simp only [d20913, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20969 q = 1) (hb : d146836 q = 1) : d151358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20970 q = 1) (hb : d146836 q = 1) : d151359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20970, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20971 q = 1) (hb : d146836 q = 1) : d151360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20972 q = 1) (hb : d146836 q = 1) : d151361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194340 q = 1) : d152628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194340, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194340, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro46332 (p : Pattern) (ha : d146836 p = 1) (hb : d194350 p = 1) : d152638 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d146836 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d146836 q = 1) : d151334 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45733 q ha hb
    | true =>
      simp only [d20945, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194346 q = 1) : d152634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194346, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194346, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194347 q = 1) : d152635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194347, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194347, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194348 q = 1) : d152636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194348, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194348, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194349 q = 1) : d152637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194349, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194349, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194350 q = 1) : d152638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194350, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194350, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46333 (p : Pattern) (ha : d146836 p = 1) (hb : d194356 p = 1) : d152644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d146836 q = 1) : d151363 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45736 q ha hb
    | true =>
      simp only [d20974, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45737 q ha hb
  have h2 (q : Pattern) (ha : d20975 q = 1) (hb : d146836 q = 1) : d151364 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194338 q = 1) : d152626 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194338, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194338, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194339 q = 1) : d152627 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194339, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194339, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194341 q = 1) : d152629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194341, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194341, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46331 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194342 q = 1) : d152630 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194342, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194342, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194343 q = 1) : d152631 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194343, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194343, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194344 q = 1) : d152632 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194344, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194344, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d194345 q = 1) : d152633 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194345, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194345, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d194351 q = 1) : d152639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194351, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194351, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46332 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d194352 q = 1) : d152640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194352, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194352, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194353 q = 1) : d152641 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194353, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194353, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194354 q = 1) : d152642 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194354, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194354, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d194355 q = 1) : d152643 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194355, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194355, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d194356 q = 1) : d152644 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194356, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194356, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46334 (p : Pattern) (ha : d146836 p = 1) (hb : d194362 p = 1) : d152650 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d146836 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194357 q = 1) : d152645 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194357, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194357, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46333 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194358 q = 1) : d152646 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194358, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194358, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194359 q = 1) : d152647 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194359, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194359, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194360 q = 1) : d152648 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194360, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194360, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194361 q = 1) : d152649 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194361, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194361, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194362 q = 1) : d152650 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194362, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194362, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro46335 (p : Pattern) (ha : d146836 p = 1) (hb : d194365 p = 1) : d152653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21156 q = 1) (hb : d146836 q = 1) : d151498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45764 q ha hb
    | true =>
      simp only [d21156, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45765 q ha hb
  have h2 (q : Pattern) (ha : d21157 q = 1) (hb : d146836 q = 1) : d151499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21158 q = 1) (hb : d146836 q = 1) : d151500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21158, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21159 q = 1) (hb : d146836 q = 1) : d151501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21160 q = 1) (hb : d146836 q = 1) : d151502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194365 q = 1) : d152653 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194365, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194365, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46336 (p : Pattern) (ha : d146836 p = 1) (hb : d194376 p = 1) : d152664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194371 q = 1) : d152659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194371, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45796 q hb ha
    | true =>
      simp only [d194371, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45771 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194372 q = 1) : d152660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194372, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194372, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194373 q = 1) : d152661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194373, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194373, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194374 q = 1) : d152662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194374, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194374, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194375 q = 1) : d152663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194375, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194375, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194376 q = 1) : d152664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194376, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194376, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46337 (p : Pattern) (ha : d146836 p = 1) (hb : d194382 p = 1) : d152670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d146836 q = 1) : d151504 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45763 q ha hb
    | true =>
      simp only [d21162, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45766 q ha hb
  have h2 (q : Pattern) (ha : d21163 q = 1) (hb : d146836 q = 1) : d151505 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194363 q = 1) : d152651 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194363, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194363, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194364 q = 1) : d152652 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194364, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194364, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194366 q = 1) : d152654 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194366, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194366, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46335 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194367 q = 1) : d152655 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194367, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194367, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194368 q = 1) : d152656 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194368, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194368, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194369 q = 1) : d152657 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194369, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194369, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d194370 q = 1) : d152658 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194370, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194370, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d194377 q = 1) : d152665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194377, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194377, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46336 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d194378 q = 1) : d152666 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194378, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194378, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194379 q = 1) : d152667 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194379, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194379, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194380 q = 1) : d152668 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194380, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194380, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d194381 q = 1) : d152669 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194381, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194381, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d194382 q = 1) : d152670 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194382, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194382, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46338 (p : Pattern) (ha : d146836 p = 1) (hb : d194388 p = 1) : d152676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194383 q = 1) : d152671 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194383, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194383, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46337 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194384 q = 1) : d152672 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194384, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194384, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194385 q = 1) : d152673 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194385, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194385, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194386 q = 1) : d152674 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194386, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194386, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194387 q = 1) : d152675 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194387, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194387, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194388 q = 1) : d152676 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194388, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194388, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46339 (p : Pattern) (ha : d146836 p = 1) (hb : d194392 p = 1) : d152680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21455 q = 1) (hb : d146836 q = 1) : d151696 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45808 q ha hb
    | true =>
      simp only [d21455, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45809 q ha hb
  have h2 (q : Pattern) (ha : d21456 q = 1) (hb : d146836 q = 1) : d151697 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21457 q = 1) (hb : d146836 q = 1) : d151698 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21457, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21458 q = 1) (hb : d146836 q = 1) : d151699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21459 q = 1) (hb : d146836 q = 1) : d151700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194392 q = 1) : d152680 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194392, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194392, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46340 (p : Pattern) (ha : d146836 p = 1) (hb : d194403 p = 1) : d152691 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194398 q = 1) : d152686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194398, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45842 q hb ha
    | true =>
      simp only [d194398, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45816 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194399 q = 1) : d152687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194399, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194399, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194400 q = 1) : d152688 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194400, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194400, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194401 q = 1) : d152689 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194401, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194401, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194402 q = 1) : d152690 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194402, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194402, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194403 q = 1) : d152691 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194403, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194403, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46341 (p : Pattern) (ha : d146836 p = 1) (hb : d194409 p = 1) : d152697 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d146836 q = 1) : d151702 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45807 q ha hb
    | true =>
      simp only [d21461, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45810 q ha hb
  have h2 (q : Pattern) (ha : d21462 q = 1) (hb : d146836 q = 1) : d151703 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194390 q = 1) : d152678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194390, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194390, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194391 q = 1) : d152679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194391, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194391, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194393 q = 1) : d152681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194393, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194393, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46339 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194394 q = 1) : d152682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194394, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194394, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194395 q = 1) : d152683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194395, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194395, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194396 q = 1) : d152684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194396, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194396, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d194397 q = 1) : d152685 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194397, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194397, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d194404 q = 1) : d152692 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194404, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194404, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46340 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d194405 q = 1) : d152693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194405, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194405, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194406 q = 1) : d152694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194406, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194406, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194407 q = 1) : d152695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194407, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194407, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d194408 q = 1) : d152696 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194408, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194408, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d194409 q = 1) : d152697 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194409, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194409, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46342 (p : Pattern) (ha : d146836 p = 1) (hb : d194415 p = 1) : d152703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194410 q = 1) : d152698 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194410, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194410, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46341 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194411 q = 1) : d152699 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194411, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194411, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194412 q = 1) : d152700 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194412, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194412, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194413 q = 1) : d152701 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194413, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194413, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194414 q = 1) : d152702 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194414, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194414, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194415 q = 1) : d152703 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194415, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194415, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46343 (p : Pattern) (ha : d146836 p = 1) (hb : d194420 p = 1) : d152708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21808 q = 1) (hb : d146836 q = 1) : d151906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45856 q ha hb
    | true =>
      simp only [d21808, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45857 q ha hb
  have h2 (q : Pattern) (ha : d21809 q = 1) (hb : d146836 q = 1) : d151907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21809, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21810 q = 1) (hb : d146836 q = 1) : d151908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21810, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21811 q = 1) (hb : d146836 q = 1) : d151909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21812 q = 1) (hb : d146836 q = 1) : d151910 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194420 q = 1) : d152708 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194420, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194420, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46344 (p : Pattern) (ha : d146836 p = 1) (hb : d194427 p = 1) : d152067 p = 1 := by
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
  have h8 (q : Pattern) (ha : d22098 q = 1) (hb : d146836 q = 1) : d152052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45864 q ha hb
    | true =>
      simp only [d22098, d152052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45865 q ha hb
  have h9 (q : Pattern) (ha : d22099 q = 1) (hb : d146836 q = 1) : d152053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d152053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22100 q = 1) (hb : d146836 q = 1) : d152054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d152054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22101 q = 1) (hb : d146836 q = 1) : d152055 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22101, d152055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194426 q = 1) : d152066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194426, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d194426, d152066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194427 q = 1) : d152067 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194427, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194427, d152067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro46345 (p : Pattern) (ha : d146836 p = 1) (hb : d194433 p = 1) : d152717 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194428 q = 1) : d152068 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194428, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46344 q ha hb
    | true =>
      simp only [d194428, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194429 q = 1) : d152069 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194429, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194429, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194430 q = 1) : d152714 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194430, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194430, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194431 q = 1) : d152715 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194431, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194431, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194432 q = 1) : d152716 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194432, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194432, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194433 q = 1) : d152717 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194433, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194433, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46346 (p : Pattern) (ha : d146836 p = 1) (hb : d194439 p = 1) : d152723 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194434 q = 1) : d152718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194434, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46345 q ha hb
    | true =>
      simp only [d194434, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45867 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194435 q = 1) : d152719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194435, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194435, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194436 q = 1) : d152720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194436, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194436, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194437 q = 1) : d152721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194437, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194437, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194438 q = 1) : d152722 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194438, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194438, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194439 q = 1) : d152723 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194439, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194439, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46347 (p : Pattern) (ha : d146836 p = 1) (hb : d194445 p = 1) : d152729 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d146836 q = 1) : d151912 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45855 q ha hb
    | true =>
      simp only [d21814, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45858 q ha hb
  have h2 (q : Pattern) (ha : d21815 q = 1) (hb : d146836 q = 1) : d151913 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194418 q = 1) : d152706 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194418, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194418, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194419 q = 1) : d152707 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194419, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194419, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194421 q = 1) : d152709 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194421, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194421, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46343 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194422 q = 1) : d152710 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194422, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194422, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194423 q = 1) : d152711 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194423, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194423, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194424 q = 1) : d152712 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194424, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194424, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d194425 q = 1) : d152713 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194425, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194425, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d194440 q = 1) : d152724 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194440, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194440, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46346 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d194441 q = 1) : d152725 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194441, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194441, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194442 q = 1) : d152726 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194442, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194442, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194443 q = 1) : d152727 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194443, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194443, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d194444 q = 1) : d152728 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194444, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194444, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d194445 q = 1) : d152729 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194445, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194445, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46348 (p : Pattern) (ha : d146836 p = 1) (hb : d194451 p = 1) : d152735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194446 q = 1) : d152730 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194446, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194446, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46347 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194447 q = 1) : d152731 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194447, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194447, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194448 q = 1) : d152732 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194448, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194448, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194449 q = 1) : d152733 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194449, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194449, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194450 q = 1) : d152734 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194450, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194450, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194451 q = 1) : d152735 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194451, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194451, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46349 (p : Pattern) (ha : d146836 p = 1) (hb : d194457 p = 1) : d152741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22286 q = 1) (hb : d146836 q = 1) : d152144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45911 q ha hb
    | true =>
      simp only [d22286, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45912 q ha hb
  have h2 (q : Pattern) (ha : d22287 q = 1) (hb : d146836 q = 1) : d152145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22287, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22288 q = 1) (hb : d146836 q = 1) : d152146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22288, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22289 q = 1) (hb : d146836 q = 1) : d152147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22290 q = 1) (hb : d146836 q = 1) : d152148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194457 q = 1) : d152741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194457, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194457, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46350 (p : Pattern) (ha : d146836 p = 1) (hb : d194464 p = 1) : d152305 p = 1 := by
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
  have h8 (q : Pattern) (ha : d22563 q = 1) (hb : d146836 q = 1) : d152290 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45919 q ha hb
    | true =>
      simp only [d22563, d152290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45920 q ha hb
  have h9 (q : Pattern) (ha : d22564 q = 1) (hb : d146836 q = 1) : d152291 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d152291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22565 q = 1) (hb : d146836 q = 1) : d152292 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d152292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22566 q = 1) (hb : d146836 q = 1) : d152293 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22566, d152293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194463 q = 1) : d152304 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194463, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d194463, d152304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194464 q = 1) : d152305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194464, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194464, d152305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro46351 (p : Pattern) (ha : d146836 p = 1) (hb : d194470 p = 1) : d152750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194465 q = 1) : d152306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194465, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46350 q ha hb
    | true =>
      simp only [d194465, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194466 q = 1) : d152307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194466, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194466, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194467 q = 1) : d152747 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194467, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194467, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194468 q = 1) : d152748 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194468, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194468, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194469 q = 1) : d152749 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194469, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194469, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194470 q = 1) : d152750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194470, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194470, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46352 (p : Pattern) (ha : d146836 p = 1) (hb : d194476 p = 1) : d152756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194471 q = 1) : d152751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194471, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46351 q ha hb
    | true =>
      simp only [d194471, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45922 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194472 q = 1) : d152752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194472, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194472, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194473 q = 1) : d152753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194473, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194473, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194474 q = 1) : d152754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194474, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194474, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194475 q = 1) : d152755 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194475, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194475, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194476 q = 1) : d152756 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194476, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194476, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46353 (p : Pattern) (ha : d146836 p = 1) (hb : d194482 p = 1) : d152762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d146836 q = 1) : d152150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45910 q ha hb
    | true =>
      simp only [d22292, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45913 q ha hb
  have h2 (q : Pattern) (ha : d22293 q = 1) (hb : d146836 q = 1) : d152151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194455 q = 1) : d152739 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194455, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194455, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194456 q = 1) : d152740 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194456, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194456, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194458 q = 1) : d152742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194458, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194458, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46349 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194459 q = 1) : d152743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194459, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194459, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194460 q = 1) : d152744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194460, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194460, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194461 q = 1) : d152745 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194461, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194461, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d194462 q = 1) : d152746 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194462, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194462, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d194477 q = 1) : d152757 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194477, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194477, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46352 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d194478 q = 1) : d152758 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194478, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194478, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194479 q = 1) : d152759 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194479, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194479, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194480 q = 1) : d152760 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194480, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194480, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d194481 q = 1) : d152761 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194481, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194481, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d194482 q = 1) : d152762 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194482, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194482, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46354 (p : Pattern) (ha : d146836 p = 1) (hb : d194488 p = 1) : d152768 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194483 q = 1) : d152763 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194483, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194483, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46353 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194484 q = 1) : d152764 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194484, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194484, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194485 q = 1) : d152765 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194485, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194485, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194486 q = 1) : d152766 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194486, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194486, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194487 q = 1) : d152767 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194487, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194487, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194488 q = 1) : d152768 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194488, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194488, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46355 (p : Pattern) (ha : d146836 p = 1) (hb : d194495 p = 1) : d152775 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22741 q = 1) (hb : d146836 q = 1) : d152383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45966 q ha hb
    | true =>
      simp only [d22741, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45967 q ha hb
  have h2 (q : Pattern) (ha : d22742 q = 1) (hb : d146836 q = 1) : d152384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22742, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22743 q = 1) (hb : d146836 q = 1) : d152385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22743, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22744 q = 1) (hb : d146836 q = 1) : d152386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22745 q = 1) (hb : d146836 q = 1) : d152387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194495 q = 1) : d152775 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194495, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194495, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  exact h6 p ha hb
theorem andIntro46356 (p : Pattern) (ha : d146836 p = 1) (hb : d194502 p = 1) : d152542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d146836 q = 1) : d152506 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46000 q ha hb
    | true =>
      simp only [d22949, d152506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d146836 q = 1) : d152507 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d152507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d146836 q = 1) : d152508 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d152508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22958 q = 1) (hb : d146836 q = 1) : d152510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d22958, d152510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46002 q ha hb
  have h5 (q : Pattern) (ha : d22959 q = 1) (hb : d146836 q = 1) : d152511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d152511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22960 q = 1) (hb : d146836 q = 1) : d152512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d152512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22961 q = 1) (hb : d146836 q = 1) : d152513 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d152513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22977 q = 1) (hb : d146836 q = 1) : d152527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45974 q ha hb
    | true =>
      simp only [d22977, d152527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45975 q ha hb
  have h9 (q : Pattern) (ha : d22978 q = 1) (hb : d146836 q = 1) : d152528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d152528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22979 q = 1) (hb : d146836 q = 1) : d152529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d152529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22980 q = 1) (hb : d146836 q = 1) : d152530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22980, d152530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194501 q = 1) : d152541 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d194501, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d194501, d152541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194502 q = 1) : d152542 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d194502, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194502, d152542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro46357 (p : Pattern) (ha : d146836 p = 1) (hb : d194508 p = 1) : d152784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194503 q = 1) : d152543 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d194503, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46356 q ha hb
    | true =>
      simp only [d194503, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194504 q = 1) : d152544 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d194504, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194504, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d146836 q = 1) : d152533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45976 q ha hb
    | true =>
      simp only [d22983, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d146836 q = 1) : d152534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194505 q = 1) : d152781 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d194505, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194505, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194506 q = 1) : d152782 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d194506, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194506, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194507 q = 1) : d152783 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d194507, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194507, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194508 q = 1) : d152784 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d194508, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194508, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46358 (p : Pattern) (ha : d146836 p = 1) (hb : d194514 p = 1) : d152790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194509 q = 1) : d152785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d194509, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46357 q ha hb
    | true =>
      simp only [d194509, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45977 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194510 q = 1) : d152786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d194510, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194510, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194511 q = 1) : d152787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d194511, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194511, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194512 q = 1) : d152788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d194512, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194512, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194513 q = 1) : d152789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d194513, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194513, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194514 q = 1) : d152790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d194514, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194514, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46359 (p : Pattern) (ha : d146836 p = 1) (hb : d194520 p = 1) : d152796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d146836 q = 1) : d152389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45965 q ha hb
    | true =>
      simp only [d22747, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45968 q ha hb
  have h2 (q : Pattern) (ha : d22748 q = 1) (hb : d146836 q = 1) : d152390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194493 q = 1) : d152773 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194493, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d194493, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194494 q = 1) : d152774 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194494, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194494, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194496 q = 1) : d152776 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194496, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194496, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46355 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194497 q = 1) : d152777 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194497, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194497, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194498 q = 1) : d152778 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194498, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194498, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194499 q = 1) : d152779 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194499, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d194499, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d194500 q = 1) : d152780 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194500, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194500, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d194515 q = 1) : d152791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d194515, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194515, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46358 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d194516 q = 1) : d152792 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d194516, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194516, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194517 q = 1) : d152793 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d194517, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d194517, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194518 q = 1) : d152794 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d194518, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d194518, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d194519 q = 1) : d152795 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d194519, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d194519, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d194520 q = 1) : d152796 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d194520, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d194520, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46360 (p : Pattern) (ha : d146836 p = 1) (hb : d194526 p = 1) : d152802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194521 q = 1) : d152797 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d194521, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194521, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46359 q ha hb
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194522 q = 1) : d152798 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d194522, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194522, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194523 q = 1) : d152799 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d194523, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194523, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194524 q = 1) : d152800 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d194524, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194524, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194525 q = 1) : d152801 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d194525, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194525, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194526 q = 1) : d152802 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d194526, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194526, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46361 (p : Pattern) (ha : d146836 p = 1) (hb : d194532 p = 1) : d152808 p = 1 := by
  have h0 (q : Pattern) (ha : d146836 q = 1) (hb : d194389 q = 1) : d152677 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194389, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46334 q ha hb
    | true =>
      simp only [d194389, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46338 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194416 q = 1) : d152704 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194416, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194416, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46342 q ha hb
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194417 q = 1) : d152705 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194417, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d194417, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194452 q = 1) : d152736 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194452, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194452, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46348 q ha hb
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194453 q = 1) : d152737 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194453, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194453, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194454 q = 1) : d152738 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194454, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194454, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146836 q = 1) (hb : d194489 q = 1) : d152769 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194489, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194489, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46354 q ha hb
  have h8 (q : Pattern) (ha : d146836 q = 1) (hb : d194490 q = 1) : d152770 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194490, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194490, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146836 q = 1) (hb : d194491 q = 1) : d152771 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194491, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194491, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146836 q = 1) (hb : d194492 q = 1) : d152772 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194492, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d194492, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d146836 q = 1) (hb : d194527 q = 1) : d152803 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d194527, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194527, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46360 q ha hb
  have h12 (q : Pattern) (ha : d146836 q = 1) (hb : d194528 q = 1) : d152804 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d194528, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194528, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146836 q = 1) (hb : d194529 q = 1) : d152805 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d194529, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194529, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d146836 q = 1) (hb : d194530 q = 1) : d152806 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d194530, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d194530, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d146836 q = 1) (hb : d194531 q = 1) : d152807 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d194531, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d194531, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d146836 q = 1) (hb : d194532 q = 1) : d152808 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d194532, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d194532, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro46362 (p : Pattern) (ha : d146836 p = 1) (hb : d194538 p = 1) : d152814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194533 q = 1) : d152809 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d194533, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46361 q ha hb
    | true =>
      simp only [d194533, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194534 q = 1) : d152810 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d194534, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194534, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194535 q = 1) : d152811 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d194535, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194535, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194536 q = 1) : d152812 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d194536, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194536, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194537 q = 1) : d152813 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d194537, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194537, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194538 q = 1) : d152814 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d194538, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194538, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46363 (p : Pattern) (ha : d146836 p = 1) (hb : d194544 p = 1) : d152820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194539 q = 1) : d152815 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d194539, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46362 q ha hb
    | true =>
      simp only [d194539, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194540 q = 1) : d152816 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d194540, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194540, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194541 q = 1) : d152817 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d194541, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194541, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194542 q = 1) : d152818 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d194542, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194542, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194543 q = 1) : d152819 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d194543, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194543, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194544 q = 1) : d152820 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d194544, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194544, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46364 (p : Pattern) (ha : d146836 p = 1) (hb : d194550 p = 1) : d152826 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194545 q = 1) : d152821 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d194545, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46363 q ha hb
    | true =>
      simp only [d194545, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194546 q = 1) : d152822 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d194546, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194546, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194547 q = 1) : d152823 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d194547, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194547, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194548 q = 1) : d152824 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d194548, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194548, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194549 q = 1) : d152825 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d194549, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194549, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194550 q = 1) : d152826 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d194550, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194550, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46365 (p : Pattern) (ha : d146836 p = 1) (hb : d194556 p = 1) : d152832 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194551 q = 1) : d152827 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46364 q ha hb
    | true =>
      simp only [d194551, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194552 q = 1) : d152828 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194553 q = 1) : d152829 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194554 q = 1) : d152830 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194555 q = 1) : d152831 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194556 q = 1) : d152832 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46366 (p : Pattern) (ha : d146836 p = 1) (hb : d194562 p = 1) : d152838 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194557 q = 1) : d152833 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46365 q ha hb
    | true =>
      simp only [d194557, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194558 q = 1) : d152834 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194559 q = 1) : d152835 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194560 q = 1) : d152836 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194561 q = 1) : d152837 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194562 q = 1) : d152838 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46367 (p : Pattern) (ha : d146836 p = 1) (hb : d194568 p = 1) : d152844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194563 q = 1) : d152839 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46366 q ha hb
    | true =>
      simp only [d194563, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194564 q = 1) : d152840 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194565 q = 1) : d152841 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194566 q = 1) : d152842 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194567 q = 1) : d152843 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194568 q = 1) : d152844 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46368 (p : Pattern) (ha : d146836 p = 1) (hb : d194574 p = 1) : d152850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146836 q = 1) (hb : d194569 q = 1) : d152845 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46367 q ha hb
    | true =>
      simp only [d194569, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d146836 q = 1) (hb : d194570 q = 1) : d152846 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d146836 q = 1) (hb : d194571 q = 1) : d152847 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d146836 q = 1) (hb : d194572 q = 1) : d152848 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d146836 q = 1) (hb : d194573 q = 1) : d152849 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d146836 q = 1) (hb : d194574 q = 1) : d152850 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46369 (p : Pattern) (ha : d112800 p = 1) (hb : d151355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112789 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112698 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46022 q ha hb
    | true =>
      simp only [d112698, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d112790 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112790, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112797 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112797, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d112798 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112798, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112799 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112799, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112800 q = 1) (hb : d151355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112800, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112800, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46370 (p : Pattern) (ha : d112819 p = 1) (hb : d151362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112769 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112698 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46022 q ha hb
    | true =>
      simp only [d112698, d151297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d112790 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112790, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112796 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d112797 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112797, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112798 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112798, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112799 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112799, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112805 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112809 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d112811 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d112705 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46024 q ha hb
    | true =>
      simp only [d112705, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d112812 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d112812, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112816 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112816, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112817 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112817, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d112817, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112818 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112818, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d112818, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112819 q = 1) (hb : d151362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112819, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112819, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46371 (p : Pattern) (ha : d112828 p = 1) (hb : d152628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112705 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46024 q ha hb
    | true =>
      simp only [d112705, d151304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d112812 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112812, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112815 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112816 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112816, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112826 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112826, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112826, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112827 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112827, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112827, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112828 q = 1) (hb : d152628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112828, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112828, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46372 (p : Pattern) (ha : d112858 p = 1) (hb : d152638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112847 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112732 q = 1) (hb : d151334 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112732, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46029 q ha hb
    | true =>
      simp only [d112732, d151334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d112848 q = 1) (hb : d152634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112848, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112848, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112854 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112855 q = 1) (hb : d152635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112855, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112855, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112856 q = 1) (hb : d152636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112856, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112856, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112857 q = 1) (hb : d152637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112857, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112857, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112858 q = 1) (hb : d152638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112858, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112858, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46373 (p : Pattern) (ha : d112864 p = 1) (hb : d152644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112763 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112820 q = 1) (hb : d151363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112820, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46369 q ha hb
    | true =>
      simp only [d112820, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46370 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112822 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112823 q = 1) (hb : d151364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112823, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112823, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112824 q = 1) (hb : d152626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112824, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112824, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112825 q = 1) (hb : d152627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112825, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112825, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112829 q = 1) (hb : d152629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112829, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112829, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46371 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112830 q = 1) (hb : d152630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112830, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112830, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d112831 q = 1) (hb : d152631 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112831, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112831, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d112832 q = 1) (hb : d152632 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112832, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112832, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d112833 q = 1) (hb : d152633 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112833, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112833, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112859 q = 1) (hb : d152639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112859, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112859, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46372 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112860 q = 1) (hb : d152640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112860, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112860, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112861 q = 1) (hb : d152641 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112861, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112861, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d112862 q = 1) (hb : d152642 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112862, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112862, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d112863 q = 1) (hb : d152643 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112863, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112863, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d112864 q = 1) (hb : d152644 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112864, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d112864, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46374 (p : Pattern) (ha : d112870 p = 1) (hb : d152650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d112744 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d112744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d112744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18822 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d112745 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d112745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d112745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d112746 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d112746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d112746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d112747 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d112747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d112747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d112748 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d112748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d112748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112865 q = 1) (hb : d152645 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112865, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112865, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46373 q ha hb
  have h8 (q : Pattern) (ha : d112866 q = 1) (hb : d152646 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112866, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112866, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112867 q = 1) (hb : d152647 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112867, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112867, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112868 q = 1) (hb : d152648 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112868, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112868, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112869 q = 1) (hb : d152649 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112869, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112869, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112870 q = 1) (hb : d152650 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d112870, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d112870, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro46375 (p : Pattern) (ha : d112954 p = 1) (hb : d151493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112922 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112943 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d112887 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46058 q ha hb
    | true =>
      simp only [d112887, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46059 q ha hb
  have h5 (q : Pattern) (ha : d112944 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d112944, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d112950 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d112951 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112951, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d112952 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112952, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112953 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112953, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112954 q = 1) (hb : d151493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112954, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112954, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46376 (p : Pattern) (ha : d112975 p = 1) (hb : d151503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112913 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112943 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112887 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46058 q ha hb
    | true =>
      simp only [d112887, d151488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46059 q ha hb
  have h4 (q : Pattern) (ha : d112944 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d112944, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112950 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d112951 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112951, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112952 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112952, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112953 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112953, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112960 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d112965 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d112967 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d112897 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46061 q ha hb
    | true =>
      simp only [d112897, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46062 q ha hb
  have h13 (q : Pattern) (ha : d112968 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d112968, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d112971 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d112972 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112972, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d112973 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112973, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d112973, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112974 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112974, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d112974, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112975 q = 1) (hb : d151503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112975, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112975, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46377 (p : Pattern) (ha : d112995 p = 1) (hb : d152653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112967 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112897 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46061 q ha hb
    | true =>
      simp only [d112897, d151498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46062 q ha hb
  have h3 (q : Pattern) (ha : d112968 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d112968, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112971 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112972 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112972, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112993 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112993, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112993, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112994 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112994, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112994, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112995 q = 1) (hb : d152653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112995, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112995, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46378 (p : Pattern) (ha : d113053 p = 1) (hb : d152664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113042 q = 1) (hb : d152659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113042, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46093 q ha hb
    | true =>
      simp only [d113042, d152659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46096 q ha hb
  have h3 (q : Pattern) (ha : d113043 q = 1) (hb : d152660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113043, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113043, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113049 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113050 q = 1) (hb : d152661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113050, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113050, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113051 q = 1) (hb : d152662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113051, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113051, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113052 q = 1) (hb : d152663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113052, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113052, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113053 q = 1) (hb : d152664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113053, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113053, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46379 (p : Pattern) (ha : d113066 p = 1) (hb : d152670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112905 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112976 q = 1) (hb : d151504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112976, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46375 q ha hb
    | true =>
      simp only [d112976, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46376 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112989 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112990 q = 1) (hb : d151505 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112990, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112990, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d112991 q = 1) (hb : d152651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112991, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112991, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112992 q = 1) (hb : d152652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112992, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112992, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112996 q = 1) (hb : d152654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112996, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112996, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46377 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d112998 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d112999 q = 1) (hb : d152655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112999, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112999, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113000 q = 1) (hb : d152656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113000, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113000, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113001 q = 1) (hb : d152657 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113001, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113001, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113002 q = 1) (hb : d152658 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113002, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113002, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113054 q = 1) (hb : d152665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113054, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113054, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46378 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113062 q = 1) (hb : d152666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113062, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113062, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113063 q = 1) (hb : d152667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113063, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113063, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113064 q = 1) (hb : d152668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113064, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113064, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113065 q = 1) (hb : d152669 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113065, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113065, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113066 q = 1) (hb : d152670 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113066, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113066, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46380 (p : Pattern) (ha : d113072 p = 1) (hb : d152676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113067 q = 1) (hb : d152671 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113067, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113067, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46379 q ha hb
  have h2 (q : Pattern) (ha : d113068 q = 1) (hb : d152672 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113068, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113068, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113069 q = 1) (hb : d152673 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113069, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113069, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113070 q = 1) (hb : d152674 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113070, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113070, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113071 q = 1) (hb : d152675 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113071, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113071, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113072 q = 1) (hb : d152676 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113072, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113072, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46381 (p : Pattern) (ha : d113161 p = 1) (hb : d151691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113150 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113094 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46103 q ha hb
    | true =>
      simp only [d113094, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46104 q ha hb
  have h5 (q : Pattern) (ha : d113151 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113151, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113157 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113158 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113158, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113159 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113159, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113160 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113160, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113161 q = 1) (hb : d151691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113161, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113161, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46382 (p : Pattern) (ha : d113182 p = 1) (hb : d151701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113120 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113150 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113094 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46103 q ha hb
    | true =>
      simp only [d113094, d151686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46104 q ha hb
  have h4 (q : Pattern) (ha : d113151 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113151, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113157 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113158 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113158, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113159 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113159, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113160 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113160, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113167 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113172 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113174 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113104 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46106 q ha hb
    | true =>
      simp only [d113104, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46107 q ha hb
  have h13 (q : Pattern) (ha : d113175 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113175, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113178 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113179 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113179, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113180 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113180, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113180, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113181 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113181, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113181, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113182 q = 1) (hb : d151701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113182, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113182, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46383 (p : Pattern) (ha : d113202 p = 1) (hb : d152680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113174 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113104 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46106 q ha hb
    | true =>
      simp only [d113104, d151696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46107 q ha hb
  have h3 (q : Pattern) (ha : d113175 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113175, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113178 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113179 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113179, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113200 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113200, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113200, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113201 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113201, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113201, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113202 q = 1) (hb : d152680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113202, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113202, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46384 (p : Pattern) (ha : d113264 p = 1) (hb : d152691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113248 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113253 q = 1) (hb : d152686 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113253, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46139 q ha hb
    | true =>
      simp only [d113253, d152686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46142 q ha hb
  have h3 (q : Pattern) (ha : d113254 q = 1) (hb : d152687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113254, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113254, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113260 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113261 q = 1) (hb : d152688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113261, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113261, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113262 q = 1) (hb : d152689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113262, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113262, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113263 q = 1) (hb : d152690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113263, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113263, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113264 q = 1) (hb : d152691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113264, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113264, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46385 (p : Pattern) (ha : d113277 p = 1) (hb : d152697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113112 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113183 q = 1) (hb : d151702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113183, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46381 q ha hb
    | true =>
      simp only [d113183, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46382 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113196 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113197 q = 1) (hb : d151703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113197, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113197, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113198 q = 1) (hb : d152678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113198, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113198, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113199 q = 1) (hb : d152679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113199, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113199, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113203 q = 1) (hb : d152681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113203, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113203, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46383 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113205 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113206 q = 1) (hb : d152682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113206, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113206, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113207 q = 1) (hb : d152683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113207, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113207, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113208 q = 1) (hb : d152684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113208, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113208, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113209 q = 1) (hb : d152685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113209, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113209, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113265 q = 1) (hb : d152692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113265, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113265, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46384 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113272 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113273 q = 1) (hb : d152693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113273, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113273, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113274 q = 1) (hb : d152694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113274, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113274, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113275 q = 1) (hb : d152695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113275, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113275, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113276 q = 1) (hb : d152696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113276, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113276, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113277 q = 1) (hb : d152697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113277, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113277, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46386 (p : Pattern) (ha : d113283 p = 1) (hb : d152703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113278 q = 1) (hb : d152698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113278, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113278, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46385 q ha hb
  have h2 (q : Pattern) (ha : d113279 q = 1) (hb : d152699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113279, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113279, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113280 q = 1) (hb : d152700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113280, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113280, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113281 q = 1) (hb : d152701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113281, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113281, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113282 q = 1) (hb : d152702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113282, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113282, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113283 q = 1) (hb : d152703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113283, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113283, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46387 (p : Pattern) (ha : d113392 p = 1) (hb : d151901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113338 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113347 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113381 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113312 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46155 q ha hb
    | true =>
      simp only [d113312, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46156 q ha hb
  have h5 (q : Pattern) (ha : d113382 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113382, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113388 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113389 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113389, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113390 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113390, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113391 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113391, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113392 q = 1) (hb : d151901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113392, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113392, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46388 (p : Pattern) (ha : d113414 p = 1) (hb : d151911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113338 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113347 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113381 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113312 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46155 q ha hb
    | true =>
      simp only [d113312, d151896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46156 q ha hb
  have h4 (q : Pattern) (ha : d113382 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113382, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113388 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113389 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113389, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113390 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113390, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113391 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113391, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113398 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113403 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113406 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113322 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46158 q ha hb
    | true =>
      simp only [d113322, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46159 q ha hb
  have h13 (q : Pattern) (ha : d113407 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113407, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113410 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113411 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113411, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113412 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113412, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113412, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113413 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113413, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113413, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113414 q = 1) (hb : d151911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113414, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113414, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46389 (p : Pattern) (ha : d113439 p = 1) (hb : d152708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113406 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113322 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46158 q ha hb
    | true =>
      simp only [d113322, d151906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46159 q ha hb
  have h3 (q : Pattern) (ha : d113407 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113407, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113410 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113411 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113411, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113437 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113437, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113437, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113438 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113438, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113438, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113439 q = 1) (hb : d152708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113439, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113439, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46390 (p : Pattern) (ha : d113503 p = 1) (hb : d152717 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113498 q = 1) (hb : d152068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113498, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46198 q ha hb
    | true =>
      simp only [d113498, d152068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113499 q = 1) (hb : d152069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113499, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113499, d152069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113489 q = 1) (hb : d152058 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113489, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46196 q ha hb
    | true =>
      simp only [d113489, d152058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113490 q = 1) (hb : d152059 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113490, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113490, d152059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113500 q = 1) (hb : d152714 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113500, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113500, d152714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113501 q = 1) (hb : d152715 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113501, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113501, d152715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113502 q = 1) (hb : d152716 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113502, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113502, d152716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113503 q = 1) (hb : d152717 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113503, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113503, d152717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46391 (p : Pattern) (ha : d113519 p = 1) (hb : d152723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113495 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113508 q = 1) (hb : d152718 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113508, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46390 q ha hb
    | true =>
      simp only [d113508, d152718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46201 q ha hb
  have h3 (q : Pattern) (ha : d113509 q = 1) (hb : d152719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113509, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113509, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113515 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113516 q = 1) (hb : d152720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113516, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113516, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113517 q = 1) (hb : d152721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113517, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113517, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113518 q = 1) (hb : d152722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113518, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113518, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113519 q = 1) (hb : d152723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113519, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113519, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46392 (p : Pattern) (ha : d113532 p = 1) (hb : d152729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113330 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113415 q = 1) (hb : d151912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113415, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46387 q ha hb
    | true =>
      simp only [d113415, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46388 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113433 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113434 q = 1) (hb : d151913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113434, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113434, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113435 q = 1) (hb : d152706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113435, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113435, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113436 q = 1) (hb : d152707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113436, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113436, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113440 q = 1) (hb : d152709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113440, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113440, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46389 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113442 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113443 q = 1) (hb : d152710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113443, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113443, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113444 q = 1) (hb : d152711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113444, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113444, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113445 q = 1) (hb : d152712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113445, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113445, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113446 q = 1) (hb : d152713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113446, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113446, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113520 q = 1) (hb : d152724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113520, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113520, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46391 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113527 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113528 q = 1) (hb : d152725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113528, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113528, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113529 q = 1) (hb : d152726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113529, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113529, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113530 q = 1) (hb : d152727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113530, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113530, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113531 q = 1) (hb : d152728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113531, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113531, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113532 q = 1) (hb : d152729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113532, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113532, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46393 (p : Pattern) (ha : d113538 p = 1) (hb : d152735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113533 q = 1) (hb : d152730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113533, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113533, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46392 q ha hb
  have h2 (q : Pattern) (ha : d113534 q = 1) (hb : d152731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113534, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113534, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113535 q = 1) (hb : d152732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113535, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113535, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113536 q = 1) (hb : d152733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113536, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113536, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113537 q = 1) (hb : d152734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113537, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113537, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113538 q = 1) (hb : d152735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113538, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113538, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46394 (p : Pattern) (ha : d113648 p = 1) (hb : d152139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113594 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113603 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113637 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113568 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46215 q ha hb
    | true =>
      simp only [d113568, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46216 q ha hb
  have h5 (q : Pattern) (ha : d113638 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113638, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113644 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113645 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113645, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113646 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113646, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113647 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113647, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113648 q = 1) (hb : d152139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113648, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113648, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46395 (p : Pattern) (ha : d113670 p = 1) (hb : d152149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113594 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113603 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113637 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113568 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46215 q ha hb
    | true =>
      simp only [d113568, d152134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46216 q ha hb
  have h4 (q : Pattern) (ha : d113638 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113638, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113644 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113645 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113645, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113646 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113646, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113647 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113647, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113654 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113659 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113662 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113578 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46218 q ha hb
    | true =>
      simp only [d113578, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46219 q ha hb
  have h13 (q : Pattern) (ha : d113663 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113663, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113666 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113667 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113667, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113668 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113668, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113668, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113669 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113669, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113669, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113670 q = 1) (hb : d152149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113670, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113670, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46396 (p : Pattern) (ha : d113695 p = 1) (hb : d152741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113578 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46218 q ha hb
    | true =>
      simp only [d113578, d152144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46219 q ha hb
  have h3 (q : Pattern) (ha : d113663 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113663, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113666 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113667 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113667, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113693 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113693, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113693, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113694 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113694, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113694, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113695 q = 1) (hb : d152741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113695, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113695, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46397 (p : Pattern) (ha : d113759 p = 1) (hb : d152750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113754 q = 1) (hb : d152306 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113754, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46258 q ha hb
    | true =>
      simp only [d113754, d152306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113755 q = 1) (hb : d152307 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113755, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113755, d152307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113745 q = 1) (hb : d152296 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46256 q ha hb
    | true =>
      simp only [d113745, d152296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113746 q = 1) (hb : d152297 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d152297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113756 q = 1) (hb : d152747 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113756, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113756, d152747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113757 q = 1) (hb : d152748 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113757, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113757, d152748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113758 q = 1) (hb : d152749 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113758, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113758, d152749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113759 q = 1) (hb : d152750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113759, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113759, d152750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46398 (p : Pattern) (ha : d113775 p = 1) (hb : d152756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113764 q = 1) (hb : d152751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113764, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46397 q ha hb
    | true =>
      simp only [d113764, d152751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46261 q ha hb
  have h3 (q : Pattern) (ha : d113765 q = 1) (hb : d152752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113765, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113765, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113772 q = 1) (hb : d152753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113772, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113772, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113773 q = 1) (hb : d152754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113773, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113773, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113774 q = 1) (hb : d152755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113774, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113774, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113775 q = 1) (hb : d152756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113775, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113775, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46399 (p : Pattern) (ha : d113788 p = 1) (hb : d152762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113586 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113671 q = 1) (hb : d152150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113671, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46394 q ha hb
    | true =>
      simp only [d113671, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46395 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113690 q = 1) (hb : d152151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113690, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113690, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113691 q = 1) (hb : d152739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113691, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113691, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113692 q = 1) (hb : d152740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113692, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113692, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113696 q = 1) (hb : d152742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113696, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113696, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46396 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113698 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113699 q = 1) (hb : d152743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113699, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113699, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113700 q = 1) (hb : d152744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113700, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113700, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113701 q = 1) (hb : d152745 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113701, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113701, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113702 q = 1) (hb : d152746 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113702, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113702, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113776 q = 1) (hb : d152757 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113776, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113776, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46398 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113783 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113784 q = 1) (hb : d152758 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113784, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113784, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113785 q = 1) (hb : d152759 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113785, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113785, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d113786 q = 1) (hb : d152760 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113786, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113786, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d113787 q = 1) (hb : d152761 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113787, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113787, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d113788 q = 1) (hb : d152762 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113788, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d113788, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46400 (p : Pattern) (ha : d113794 p = 1) (hb : d152768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113789 q = 1) (hb : d152763 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113789, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113789, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46399 q ha hb
  have h2 (q : Pattern) (ha : d113790 q = 1) (hb : d152764 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113790, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113790, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113791 q = 1) (hb : d152765 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113791, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113791, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113792 q = 1) (hb : d152766 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113792, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113792, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113793 q = 1) (hb : d152767 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113793, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113793, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113794 q = 1) (hb : d152768 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113794, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113794, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46401 (p : Pattern) (ha : d113905 p = 1) (hb : d152378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113851 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d113894 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d113825 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46275 q ha hb
    | true =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46276 q ha hb
  have h5 (q : Pattern) (ha : d113895 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d113895, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d113901 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d113902 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113902, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d113903 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113903, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113904 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113904, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113905 q = 1) (hb : d152378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113905, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113905, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46402 (p : Pattern) (ha : d113927 p = 1) (hb : d152388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113851 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113894 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113825 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46275 q ha hb
    | true =>
      simp only [d113825, d152373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46276 q ha hb
  have h4 (q : Pattern) (ha : d113895 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d113895, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113901 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113902 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113902, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113903 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113903, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113904 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113904, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113911 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113916 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113919 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d113835 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46278 q ha hb
    | true =>
      simp only [d113835, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46279 q ha hb
  have h13 (q : Pattern) (ha : d113920 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d113920, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d113923 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d113924 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113924, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113925 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113925, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d113925, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113926 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113926, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d113926, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113927 q = 1) (hb : d152388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113927, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113927, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46403 (p : Pattern) (ha : d113952 p = 1) (hb : d152775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113919 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113835 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46278 q ha hb
    | true =>
      simp only [d113835, d152383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46279 q ha hb
  have h3 (q : Pattern) (ha : d113920 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113920, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d113923 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113924 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113924, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113950 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113950, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113950, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113951 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113951, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113951, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113952 q = 1) (hb : d152775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113952, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113952, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46404 (p : Pattern) (ha : d114016 p = 1) (hb : d152784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114011 q = 1) (hb : d152543 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114011, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46316 q ha hb
    | true =>
      simp only [d114011, d152543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114012 q = 1) (hb : d152544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114012, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114012, d152544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114002 q = 1) (hb : d152533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46314 q ha hb
    | true =>
      simp only [d114002, d152533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114003 q = 1) (hb : d152534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d152534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114013 q = 1) (hb : d152781 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114013, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114013, d152781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114014 q = 1) (hb : d152782 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114014, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114014, d152782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d114015 q = 1) (hb : d152783 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114015, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d114015, d152783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d114016 q = 1) (hb : d152784 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114016, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114016, d152784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro46405 (p : Pattern) (ha : d114032 p = 1) (hb : d152790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d114008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d114021 q = 1) (hb : d152785 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114021, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46404 q ha hb
    | true =>
      simp only [d114021, d152785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46319 q ha hb
  have h3 (q : Pattern) (ha : d114022 q = 1) (hb : d152786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114022, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114022, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d114028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d114029 q = 1) (hb : d152787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114029, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114029, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d114030 q = 1) (hb : d152788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114030, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114030, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d114031 q = 1) (hb : d152789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114031, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114031, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d114032 q = 1) (hb : d152790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114032, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114032, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46406 (p : Pattern) (ha : d114045 p = 1) (hb : d152796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d113843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113928 q = 1) (hb : d152389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113928, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46401 q ha hb
    | true =>
      simp only [d113928, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46402 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113946 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113947 q = 1) (hb : d152390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113947, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113947, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d113948 q = 1) (hb : d152773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113948, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113948, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d113949 q = 1) (hb : d152774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113949, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113949, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113953 q = 1) (hb : d152776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113953, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d113953, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46403 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d113955 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d113956 q = 1) (hb : d152777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113956, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113956, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d113957 q = 1) (hb : d152778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113957, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113957, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d113958 q = 1) (hb : d152779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113958, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113958, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d113959 q = 1) (hb : d152780 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113959, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113959, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114033 q = 1) (hb : d152791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114033, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d114033, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46405 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d114040 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d114041 q = 1) (hb : d152792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d114041, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d114041, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d114042 q = 1) (hb : d152793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114042, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114042, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d114043 q = 1) (hb : d152794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d114043, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d114043, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d114044 q = 1) (hb : d152795 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d114044, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d114044, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d114045 q = 1) (hb : d152796 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d114045, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d114045, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46407 (p : Pattern) (ha : d114051 p = 1) (hb : d152802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114046 q = 1) (hb : d152797 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d114046, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114046, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46406 q ha hb
  have h2 (q : Pattern) (ha : d114047 q = 1) (hb : d152798 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d114047, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114047, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114048 q = 1) (hb : d152799 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d114048, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114048, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d114049 q = 1) (hb : d152800 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d114049, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114049, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114050 q = 1) (hb : d152801 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d114050, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114050, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114051 q = 1) (hb : d152802 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d114051, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114051, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46408 (p : Pattern) (ha : d114057 p = 1) (hb : d152808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d113073 q = 1) (hb : d152677 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113073, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46374 q ha hb
    | true =>
      simp only [d113073, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46380 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113284 q = 1) (hb : d152704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113284, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113284, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46386 q ha hb
  have h3 (q : Pattern) (ha : d113285 q = 1) (hb : d152705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113285, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d113285, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113539 q = 1) (hb : d152736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113539, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113539, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46393 q ha hb
  have h5 (q : Pattern) (ha : d113540 q = 1) (hb : d152737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113540, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113540, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113541 q = 1) (hb : d152738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113541, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113541, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113795 q = 1) (hb : d152769 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113795, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113795, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46400 q ha hb
  have h8 (q : Pattern) (ha : d113796 q = 1) (hb : d152770 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113796, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113796, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113797 q = 1) (hb : d152771 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113797, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113797, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113798 q = 1) (hb : d152772 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d113798, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113798, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d114052 q = 1) (hb : d152803 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d114052, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114052, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46407 q ha hb
  have h12 (q : Pattern) (ha : d114053 q = 1) (hb : d152804 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d114053, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114053, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114054 q = 1) (hb : d152805 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d114054, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114054, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d114055 q = 1) (hb : d152806 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d114055, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114055, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d114056 q = 1) (hb : d152807 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d114056, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d114056, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d114057 q = 1) (hb : d152808 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d114057, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114057, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro46409 (p : Pattern) (ha : d114063 p = 1) (hb : d152814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114058 q = 1) (hb : d152809 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d114058, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46408 q ha hb
    | true =>
      simp only [d114058, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114059 q = 1) (hb : d152810 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d114059, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114059, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114060 q = 1) (hb : d152811 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d114060, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114060, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114061 q = 1) (hb : d152812 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d114061, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114061, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114062 q = 1) (hb : d152813 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d114062, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114062, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114063 q = 1) (hb : d152814 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d114063, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114063, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46410 (p : Pattern) (ha : d114069 p = 1) (hb : d152820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114064 q = 1) (hb : d152815 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d114064, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46409 q ha hb
    | true =>
      simp only [d114064, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114065 q = 1) (hb : d152816 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d114065, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114065, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114066 q = 1) (hb : d152817 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d114066, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114066, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114067 q = 1) (hb : d152818 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d114067, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114067, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114068 q = 1) (hb : d152819 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d114068, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114068, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114069 q = 1) (hb : d152820 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d114069, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114069, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46411 (p : Pattern) (ha : d114075 p = 1) (hb : d152826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114070 q = 1) (hb : d152821 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d114070, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46410 q ha hb
    | true =>
      simp only [d114070, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114071 q = 1) (hb : d152822 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d114071, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114071, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114072 q = 1) (hb : d152823 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d114072, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114072, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114073 q = 1) (hb : d152824 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d114073, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114073, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114074 q = 1) (hb : d152825 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d114074, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114074, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114075 q = 1) (hb : d152826 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d114075, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114075, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46412 (p : Pattern) (ha : d114081 p = 1) (hb : d152832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114076 q = 1) (hb : d152827 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d114076, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46411 q ha hb
    | true =>
      simp only [d114076, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114077 q = 1) (hb : d152828 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d114077, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114077, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114078 q = 1) (hb : d152829 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d114078, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114078, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114079 q = 1) (hb : d152830 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d114079, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114079, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114080 q = 1) (hb : d152831 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d114080, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114080, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114081 q = 1) (hb : d152832 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d114081, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114081, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46413 (p : Pattern) (ha : d114087 p = 1) (hb : d152838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114082 q = 1) (hb : d152833 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d114082, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46412 q ha hb
    | true =>
      simp only [d114082, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114083 q = 1) (hb : d152834 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d114083, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114083, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114084 q = 1) (hb : d152835 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d114084, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114084, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114085 q = 1) (hb : d152836 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d114085, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114085, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114086 q = 1) (hb : d152837 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d114086, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114086, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114087 q = 1) (hb : d152838 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d114087, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114087, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46414 (p : Pattern) (ha : d114093 p = 1) (hb : d152844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114088 q = 1) (hb : d152839 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d114088, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46413 q ha hb
    | true =>
      simp only [d114088, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114089 q = 1) (hb : d152840 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d114089, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114089, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114090 q = 1) (hb : d152841 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d114090, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114090, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114091 q = 1) (hb : d152842 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d114091, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114091, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114092 q = 1) (hb : d152843 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d114092, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114092, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114093 q = 1) (hb : d152844 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d114093, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114093, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46415 (p : Pattern) (ha : d114099 p = 1) (hb : d152850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114094 q = 1) (hb : d152845 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d114094, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46414 q ha hb
    | true =>
      simp only [d114094, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114095 q = 1) (hb : d152846 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d114095, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114095, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114096 q = 1) (hb : d152847 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d114096, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114096, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114097 q = 1) (hb : d152848 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d114097, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114097, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114098 q = 1) (hb : d152849 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d114098, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114098, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114099 q = 1) (hb : d152850 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d114099, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114099, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro46416 (p : Pattern) (ha : d115280 p = 1) (hb : d151355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12305 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12325 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115276 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115276, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12346 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115277 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115277, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115278 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115278, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115279 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115279, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115280 q = 1) (hb : d151355 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115280, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115280, d151355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46417 (p : Pattern) (ha : d115285 p = 1) (hb : d151362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12305 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12311 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151297 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115276 q = 1) (hb : d151351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115276, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115276, d151351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12346 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115277 q = 1) (hb : d151352 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115277, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115277, d151352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115278 q = 1) (hb : d151353 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115278, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115278, d151353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115279 q = 1) (hb : d151354 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115279, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115279, d151354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12355 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12359 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12361 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115281 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115281, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12367 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115282 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115282, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115283 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115283, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115283, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115284 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115284, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115284, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115285 q = 1) (hb : d151362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115285, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115285, d151362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46418 (p : Pattern) (ha : d115292 p = 1) (hb : d152628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12361 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151304 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115281 q = 1) (hb : d151358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115281, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115281, d151358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115282 q = 1) (hb : d151359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115282, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115282, d151359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115290 q = 1) (hb : d151360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115290, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115290, d151360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115291 q = 1) (hb : d151361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115291, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115291, d151361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115292 q = 1) (hb : d152628 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115292, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115292, d152628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46419 (p : Pattern) (ha : d115302 p = 1) (hb : d152638 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12399 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151334 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115298 q = 1) (hb : d152634 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115298, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115298, d152634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12420 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115299 q = 1) (hb : d152635 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115299, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115299, d152635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115300 q = 1) (hb : d152636 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115300, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115300, d152636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115301 q = 1) (hb : d152637 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115301, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115301, d152637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115302 q = 1) (hb : d152638 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115302, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115302, d152638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46420 (p : Pattern) (ha : d115308 p = 1) (hb : d152644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12299 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115286 q = 1) (hb : d151363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115286, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46416 q ha hb
    | true =>
      simp only [d115286, d151363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46417 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115287 q = 1) (hb : d151364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115287, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115287, d151364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115288 q = 1) (hb : d152626 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115288, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115288, d152626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115289 q = 1) (hb : d152627 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115289, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115289, d152627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115293 q = 1) (hb : d152629 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115293, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115293, d152629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46418 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115294 q = 1) (hb : d152630 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115294, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115294, d152630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115295 q = 1) (hb : d152631 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115295, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115295, d152631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115296 q = 1) (hb : d152632 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115296, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115296, d152632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115297 q = 1) (hb : d152633 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115297, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115297, d152633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115303 q = 1) (hb : d152639 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115303, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115303, d152639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46419 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115304 q = 1) (hb : d152640 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115304, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115304, d152640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115305 q = 1) (hb : d152641 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115305, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115305, d152641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115306 q = 1) (hb : d152642 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115306, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115306, d152642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115307 q = 1) (hb : d152643 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115307, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115307, d152643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115308 q = 1) (hb : d152644 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115308, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115308, d152644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46421 (p : Pattern) (ha : d115314 p = 1) (hb : d152650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d115271 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d115271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18874 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d115272 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d115272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d115273 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d115273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d115274 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d115274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d115275 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d115275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115309 q = 1) (hb : d152645 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115309, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115309, d152645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46420 q ha hb
  have h8 (q : Pattern) (ha : d115310 q = 1) (hb : d152646 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115310, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115310, d152646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115311 q = 1) (hb : d152647 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115311, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115311, d152647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115312 q = 1) (hb : d152648 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115312, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115312, d152648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115313 q = 1) (hb : d152649 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115313, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115313, d152649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d115314 q = 1) (hb : d152650 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115314, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d115314, d152650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro46422 (p : Pattern) (ha : d115319 p = 1) (hb : d151493 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12479 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12488 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12509 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115315 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115315, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12539 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115316 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115316, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115317 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115317, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115318 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115318, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115319 q = 1) (hb : d151493 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115319, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115319, d151493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46423 (p : Pattern) (ha : d115324 p = 1) (hb : d151503 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12479 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12488 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151488 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115315 q = 1) (hb : d151489 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115315, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115315, d151489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12539 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115316 q = 1) (hb : d151490 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115316, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115316, d151490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115317 q = 1) (hb : d151491 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115317, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115317, d151491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115318 q = 1) (hb : d151492 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115318, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115318, d151492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12549 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12554 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12556 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115320 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115320, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12563 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115321 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115321, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115322 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115322, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115322, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115323 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115323, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115323, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115324 q = 1) (hb : d151503 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115324, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115324, d151503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46424 (p : Pattern) (ha : d115331 p = 1) (hb : d152653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12556 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151498 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115320 q = 1) (hb : d151499 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115320, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115320, d151499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12563 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115321 q = 1) (hb : d151500 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115321, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115321, d151500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115329 q = 1) (hb : d151501 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115329, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115329, d151501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115330 q = 1) (hb : d151502 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115330, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115330, d151502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115331 q = 1) (hb : d152653 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115331, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115331, d152653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46425 (p : Pattern) (ha : d115341 p = 1) (hb : d152664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12629 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152659 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115337 q = 1) (hb : d152660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115337, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115337, d152660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12659 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115338 q = 1) (hb : d152661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115338, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115338, d152661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115339 q = 1) (hb : d152662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115339, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115339, d152662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115340 q = 1) (hb : d152663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115340, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115340, d152663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115341 q = 1) (hb : d152664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115341, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115341, d152664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46426 (p : Pattern) (ha : d115347 p = 1) (hb : d152670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12471 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115325 q = 1) (hb : d151504 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115325, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46422 q ha hb
    | true =>
      simp only [d115325, d151504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46423 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12581 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115326 q = 1) (hb : d151505 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115326, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115326, d151505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115327 q = 1) (hb : d152651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115327, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115327, d152651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115328 q = 1) (hb : d152652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115328, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115328, d152652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115332 q = 1) (hb : d152654 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115332, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115332, d152654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46424 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12590 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115333 q = 1) (hb : d152655 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115333, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115333, d152655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115334 q = 1) (hb : d152656 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115334, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115334, d152656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115335 q = 1) (hb : d152657 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115335, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115335, d152657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115336 q = 1) (hb : d152658 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115336, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115336, d152658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115342 q = 1) (hb : d152665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115342, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115342, d152665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46425 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12675 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115343 q = 1) (hb : d152666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115343, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115343, d152666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115344 q = 1) (hb : d152667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115344, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115344, d152667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115345 q = 1) (hb : d152668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115345, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115345, d152668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115346 q = 1) (hb : d152669 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115346, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115346, d152669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115347 q = 1) (hb : d152670 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115347, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115347, d152670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46427 (p : Pattern) (ha : d115353 p = 1) (hb : d152676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115348 q = 1) (hb : d152671 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115348, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115348, d152671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46426 q ha hb
  have h2 (q : Pattern) (ha : d115349 q = 1) (hb : d152672 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115349, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115349, d152672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115350 q = 1) (hb : d152673 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115350, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115350, d152673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115351 q = 1) (hb : d152674 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115351, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115351, d152674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115352 q = 1) (hb : d152675 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115352, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115352, d152675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115353 q = 1) (hb : d152676 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115353, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115353, d152676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46428 (p : Pattern) (ha : d115359 p = 1) (hb : d151691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12734 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12743 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d12764 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115355 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12798 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115356 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115356, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115357 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115357, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115358 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115358, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115359 q = 1) (hb : d151691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115359, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115359, d151691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46429 (p : Pattern) (ha : d115364 p = 1) (hb : d151701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151686 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115355 q = 1) (hb : d151687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115355, d151687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12798 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115356 q = 1) (hb : d151688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115356, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115356, d151688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115357 q = 1) (hb : d151689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115357, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115357, d151689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115358 q = 1) (hb : d151690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115358, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115358, d151690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12808 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12813 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12815 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115360 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115360, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12822 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115361 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115361, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115362 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115362, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115362, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115363 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115363, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115363, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115364 q = 1) (hb : d151701 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115364, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115364, d151701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46430 (p : Pattern) (ha : d115371 p = 1) (hb : d152680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12815 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115360 q = 1) (hb : d151697 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115360, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115360, d151697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12822 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115361 q = 1) (hb : d151698 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115361, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115361, d151698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115369 q = 1) (hb : d151699 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115369, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115369, d151699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115370 q = 1) (hb : d151700 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115370, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115370, d151700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115371 q = 1) (hb : d152680 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115371, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115371, d152680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46431 (p : Pattern) (ha : d115381 p = 1) (hb : d152691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115377 q = 1) (hb : d152687 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115377, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115377, d152687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12926 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115378 q = 1) (hb : d152688 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115378, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115378, d152688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115379 q = 1) (hb : d152689 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115379, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115379, d152689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115380 q = 1) (hb : d152690 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115380, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115380, d152690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115381 q = 1) (hb : d152691 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115381, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115381, d152691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46432 (p : Pattern) (ha : d115387 p = 1) (hb : d152697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d12726 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115365 q = 1) (hb : d151702 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115365, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46428 q ha hb
    | true =>
      simp only [d115365, d151702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46429 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12840 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115366 q = 1) (hb : d151703 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115366, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115366, d151703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115367 q = 1) (hb : d152678 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115367, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115367, d152678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115368 q = 1) (hb : d152679 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115368, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115368, d152679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115372 q = 1) (hb : d152681 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115372, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115372, d152681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46430 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12849 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115373 q = 1) (hb : d152682 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115373, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115373, d152682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115374 q = 1) (hb : d152683 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115374, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115374, d152683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115375 q = 1) (hb : d152684 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115375, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115375, d152684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115376 q = 1) (hb : d152685 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115376, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115376, d152685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115382 q = 1) (hb : d152692 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115382, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115382, d152692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46431 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12942 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115383 q = 1) (hb : d152693 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115383, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115383, d152693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115384 q = 1) (hb : d152694 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115384, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115384, d152694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115385 q = 1) (hb : d152695 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115385, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115385, d152695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115386 q = 1) (hb : d152696 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115386, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115386, d152696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115387 q = 1) (hb : d152697 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115387, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115387, d152697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46433 (p : Pattern) (ha : d115393 p = 1) (hb : d152703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115388 q = 1) (hb : d152698 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115388, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115388, d152698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46432 q ha hb
  have h2 (q : Pattern) (ha : d115389 q = 1) (hb : d152699 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115389, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115389, d152699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115390 q = 1) (hb : d152700 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115390, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115390, d152700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115391 q = 1) (hb : d152701 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115391, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115391, d152701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115392 q = 1) (hb : d152702 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115392, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115392, d152702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115393 q = 1) (hb : d152703 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115393, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115393, d152703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46434 (p : Pattern) (ha : d115400 p = 1) (hb : d151901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13008 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13051 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115396 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115396, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13093 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115397 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115397, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115398 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115398, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115399 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115399, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115400 q = 1) (hb : d151901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115400, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115400, d151901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46435 (p : Pattern) (ha : d115405 p = 1) (hb : d151911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13008 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13051 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d151896 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115396 q = 1) (hb : d151897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115396, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115396, d151897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13093 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115397 q = 1) (hb : d151898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115397, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115397, d151898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115398 q = 1) (hb : d151899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115398, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115398, d151899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115399 q = 1) (hb : d151900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115399, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115399, d151900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13103 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13108 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13111 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115401 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115401, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13118 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115402 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115402, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115403 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115403, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115403, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115404 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115404, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115404, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115405 q = 1) (hb : d151911 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115405, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115405, d151911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46436 (p : Pattern) (ha : d115412 p = 1) (hb : d152708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d151906 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115401 q = 1) (hb : d151907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115401, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115401, d151907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13118 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115402 q = 1) (hb : d151908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115402, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115402, d151908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115410 q = 1) (hb : d151909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115410, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115410, d151909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115411 q = 1) (hb : d151910 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115411, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115411, d151910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115412 q = 1) (hb : d152708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115412, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115412, d152708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46437 (p : Pattern) (ha : d115422 p = 1) (hb : d152723 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152718 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115418 q = 1) (hb : d152719 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115418, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115418, d152719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13251 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115419 q = 1) (hb : d152720 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115419, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115419, d152720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115420 q = 1) (hb : d152721 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115420, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115420, d152721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115421 q = 1) (hb : d152722 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115421, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115421, d152722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115422 q = 1) (hb : d152723 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115422, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115422, d152723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46438 (p : Pattern) (ha : d115428 p = 1) (hb : d152729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13000 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115406 q = 1) (hb : d151912 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115406, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46434 q ha hb
    | true =>
      simp only [d115406, d151912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46435 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115407 q = 1) (hb : d151913 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115407, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115407, d151913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115408 q = 1) (hb : d152706 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115408, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115408, d152706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115409 q = 1) (hb : d152707 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115409, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115409, d152707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115413 q = 1) (hb : d152709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115413, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115413, d152709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46436 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13150 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115414 q = 1) (hb : d152710 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115414, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115414, d152710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115415 q = 1) (hb : d152711 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115415, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115415, d152711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115416 q = 1) (hb : d152712 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115416, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115416, d152712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115417 q = 1) (hb : d152713 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115417, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115417, d152713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115423 q = 1) (hb : d152724 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115423, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115423, d152724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46437 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13267 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115424 q = 1) (hb : d152725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115424, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115424, d152725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115425 q = 1) (hb : d152726 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115425, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115425, d152726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115426 q = 1) (hb : d152727 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115426, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115426, d152727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115427 q = 1) (hb : d152728 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115427, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115427, d152728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115428 q = 1) (hb : d152729 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115428, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115428, d152729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46439 (p : Pattern) (ha : d115434 p = 1) (hb : d152735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115429 q = 1) (hb : d152730 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115429, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115429, d152730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46438 q ha hb
  have h2 (q : Pattern) (ha : d115430 q = 1) (hb : d152731 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115430, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115430, d152731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115431 q = 1) (hb : d152732 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115431, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115431, d152732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115432 q = 1) (hb : d152733 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115432, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115432, d152733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115433 q = 1) (hb : d152734 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115433, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115433, d152734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115434 q = 1) (hb : d152735 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115434, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115434, d152735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46440 (p : Pattern) (ha : d115442 p = 1) (hb : d152139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13377 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115438 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115438, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13419 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115439 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115439, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115440 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115440, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115441 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115441, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115442 q = 1) (hb : d152139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115442, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115442, d152139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46441 (p : Pattern) (ha : d115447 p = 1) (hb : d152149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13343 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152134 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115438 q = 1) (hb : d152135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115438, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115438, d152135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13419 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115439 q = 1) (hb : d152136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115439, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115439, d152136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115440 q = 1) (hb : d152137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115440, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115440, d152137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115441 q = 1) (hb : d152138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115441, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115441, d152138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13429 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13434 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13437 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115443 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115443, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13444 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115444 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115444, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115445 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115445, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115445, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115446 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115446, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115446, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115447 q = 1) (hb : d152149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115447, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115447, d152149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46442 (p : Pattern) (ha : d115454 p = 1) (hb : d152741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13437 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115443 q = 1) (hb : d152145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115443, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115443, d152145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115444 q = 1) (hb : d152146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115444, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115444, d152146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115452 q = 1) (hb : d152147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115452, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115452, d152147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115453 q = 1) (hb : d152148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115453, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115453, d152148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115454 q = 1) (hb : d152741 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115454, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115454, d152741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46443 (p : Pattern) (ha : d115464 p = 1) (hb : d152756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13529 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152751 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115460 q = 1) (hb : d152752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115460, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115460, d152752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13577 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115461 q = 1) (hb : d152753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115461, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115461, d152753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115462 q = 1) (hb : d152754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115462, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115462, d152754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115463 q = 1) (hb : d152755 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115463, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115463, d152755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115464 q = 1) (hb : d152756 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115464, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115464, d152756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46444 (p : Pattern) (ha : d115470 p = 1) (hb : d152762 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13326 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115448 q = 1) (hb : d152150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115448, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46440 q ha hb
    | true =>
      simp only [d115448, d152150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46441 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13467 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115449 q = 1) (hb : d152151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115449, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115449, d152151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115450 q = 1) (hb : d152739 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115450, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115450, d152739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115451 q = 1) (hb : d152740 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115451, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115451, d152740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115455 q = 1) (hb : d152742 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115455, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115455, d152742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46442 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13476 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115456 q = 1) (hb : d152743 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115456, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115456, d152743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115457 q = 1) (hb : d152744 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115457, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115457, d152744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115458 q = 1) (hb : d152745 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115458, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115458, d152745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115459 q = 1) (hb : d152746 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115459, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115459, d152746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115465 q = 1) (hb : d152757 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115465, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115465, d152757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46443 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13593 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115466 q = 1) (hb : d152758 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115466, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115466, d152758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115467 q = 1) (hb : d152759 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115467, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115467, d152759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115468 q = 1) (hb : d152760 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115468, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115468, d152760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115469 q = 1) (hb : d152761 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115469, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115469, d152761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115470 q = 1) (hb : d152762 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115470, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115470, d152762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46445 (p : Pattern) (ha : d115476 p = 1) (hb : d152768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115471 q = 1) (hb : d152763 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115471, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115471, d152763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46444 q ha hb
  have h2 (q : Pattern) (ha : d115472 q = 1) (hb : d152764 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115472, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115472, d152764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115473 q = 1) (hb : d152765 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115473, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115473, d152765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115474 q = 1) (hb : d152766 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115474, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115474, d152766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115475 q = 1) (hb : d152767 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115475, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115475, d152767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115476 q = 1) (hb : d152768 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115476, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115476, d152768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46446 (p : Pattern) (ha : d115485 p = 1) (hb : d152378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13661 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13670 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d13704 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115481 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d115481, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d13746 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d115482 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115482, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d115483 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115483, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115484 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115484, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115485 q = 1) (hb : d152378 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115485, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115485, d152378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro46447 (p : Pattern) (ha : d115490 p = 1) (hb : d152388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13661 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13704 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d152373 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d115481 q = 1) (hb : d152374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115481, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d115481, d152374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d13746 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d115482 q = 1) (hb : d152375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115482, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115482, d152375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d115483 q = 1) (hb : d152376 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115483, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115483, d152376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115484 q = 1) (hb : d152377 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115484, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115484, d152377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d13756 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d13761 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d13764 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d115486 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d115486, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13771 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115487 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115487, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115488 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115488, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d115488, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d115489 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115489, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d115489, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d115490 q = 1) (hb : d152388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115490, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d115490, d152388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro46448 (p : Pattern) (ha : d115497 p = 1) (hb : d152775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115486 q = 1) (hb : d152384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115486, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115486, d152384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13771 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115487 q = 1) (hb : d152385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115487, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115487, d152385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115495 q = 1) (hb : d152386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115495, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115495, d152386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115496 q = 1) (hb : d152387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115496, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115496, d152387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115497 q = 1) (hb : d152775 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115497, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115497, d152775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46449 (p : Pattern) (ha : d115507 p = 1) (hb : d152790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13856 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d152785 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115503 q = 1) (hb : d152786 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d115503, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d115503, d152786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13904 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115504 q = 1) (hb : d152787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d115504, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115504, d152787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d115505 q = 1) (hb : d152788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d115505, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115505, d152788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115506 q = 1) (hb : d152789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d115506, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115506, d152789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d115507 q = 1) (hb : d152790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d115507, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115507, d152790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46450 (p : Pattern) (ha : d115513 p = 1) (hb : d152796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d13653 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115491 q = 1) (hb : d152389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115491, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46446 q ha hb
    | true =>
      simp only [d115491, d152389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46447 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d13794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d115492 q = 1) (hb : d152390 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115492, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115492, d152390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d115493 q = 1) (hb : d152773 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115493, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115493, d152773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115494 q = 1) (hb : d152774 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115494, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d115494, d152774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115498 q = 1) (hb : d152776 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115498, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115498, d152776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46448 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d13803 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d115499 q = 1) (hb : d152777 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115499, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d115499, d152777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d115500 q = 1) (hb : d152778 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115500, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d115500, d152778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d115501 q = 1) (hb : d152779 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115501, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115501, d152779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d115502 q = 1) (hb : d152780 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115502, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115502, d152780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115508 q = 1) (hb : d152791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d115508, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115508, d152791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46449 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d13920 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d115509 q = 1) (hb : d152792 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d115509, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d115509, d152792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d115510 q = 1) (hb : d152793 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d115510, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115510, d152793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d115511 q = 1) (hb : d152794 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d115511, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d115511, d152794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d115512 q = 1) (hb : d152795 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d115512, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d115512, d152795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d115513 q = 1) (hb : d152796 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d115513, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d115513, d152796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro46451 (p : Pattern) (ha : d115519 p = 1) (hb : d152802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115514 q = 1) (hb : d152797 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d115514, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115514, d152797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46450 q ha hb
  have h2 (q : Pattern) (ha : d115515 q = 1) (hb : d152798 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d115515, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115515, d152798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d115516 q = 1) (hb : d152799 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d115516, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115516, d152799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115517 q = 1) (hb : d152800 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d115517, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115517, d152800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d115518 q = 1) (hb : d152801 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d115518, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115518, d152801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115519 q = 1) (hb : d152802 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d115519, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115519, d152802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46452 (p : Pattern) (ha : d115525 p = 1) (hb : d152808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d115354 q = 1) (hb : d152677 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115354, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46421 q ha hb
    | true =>
      simp only [d115354, d152677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46427 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d115394 q = 1) (hb : d152704 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115394, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115394, d152704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46433 q ha hb
  have h3 (q : Pattern) (ha : d115395 q = 1) (hb : d152705 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115395, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d115395, d152705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d115435 q = 1) (hb : d152736 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115435, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115435, d152736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46439 q ha hb
  have h5 (q : Pattern) (ha : d115436 q = 1) (hb : d152737 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115436, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115436, d152737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d115437 q = 1) (hb : d152738 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115437, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115437, d152738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d115477 q = 1) (hb : d152769 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115477, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115477, d152769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46445 q ha hb
  have h8 (q : Pattern) (ha : d115478 q = 1) (hb : d152770 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115478, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115478, d152770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d115479 q = 1) (hb : d152771 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115479, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115479, d152771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d115480 q = 1) (hb : d152772 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115480, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d115480, d152772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d115520 q = 1) (hb : d152803 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d115520, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115520, d152803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46451 q ha hb
  have h12 (q : Pattern) (ha : d115521 q = 1) (hb : d152804 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d115521, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115521, d152804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d115522 q = 1) (hb : d152805 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d115522, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115522, d152805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d115523 q = 1) (hb : d152806 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d115523, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115523, d152806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d115524 q = 1) (hb : d152807 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d115524, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d115524, d152807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d115525 q = 1) (hb : d152808 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d115525, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d115525, d152808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro46453 (p : Pattern) (ha : d115531 p = 1) (hb : d152814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115526 q = 1) (hb : d152809 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d115526, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46452 q ha hb
    | true =>
      simp only [d115526, d152809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115527 q = 1) (hb : d152810 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d115527, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115527, d152810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115528 q = 1) (hb : d152811 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d115528, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115528, d152811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115529 q = 1) (hb : d152812 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d115529, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115529, d152812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115530 q = 1) (hb : d152813 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d115530, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115530, d152813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115531 q = 1) (hb : d152814 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d115531, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115531, d152814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46454 (p : Pattern) (ha : d115537 p = 1) (hb : d152820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115532 q = 1) (hb : d152815 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d115532, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46453 q ha hb
    | true =>
      simp only [d115532, d152815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115533 q = 1) (hb : d152816 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d115533, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115533, d152816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115534 q = 1) (hb : d152817 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d115534, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115534, d152817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115535 q = 1) (hb : d152818 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d115535, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115535, d152818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115536 q = 1) (hb : d152819 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d115536, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115536, d152819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115537 q = 1) (hb : d152820 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d115537, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115537, d152820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46455 (p : Pattern) (ha : d115543 p = 1) (hb : d152826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115538 q = 1) (hb : d152821 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d115538, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46454 q ha hb
    | true =>
      simp only [d115538, d152821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115539 q = 1) (hb : d152822 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d115539, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115539, d152822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115540 q = 1) (hb : d152823 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d115540, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115540, d152823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115541 q = 1) (hb : d152824 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d115541, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115541, d152824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115542 q = 1) (hb : d152825 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d115542, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115542, d152825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115543 q = 1) (hb : d152826 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d115543, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115543, d152826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46456 (p : Pattern) (ha : d115549 p = 1) (hb : d152832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115544 q = 1) (hb : d152827 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d115544, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46455 q ha hb
    | true =>
      simp only [d115544, d152827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115545 q = 1) (hb : d152828 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d115545, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115545, d152828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115546 q = 1) (hb : d152829 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d115546, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115546, d152829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115547 q = 1) (hb : d152830 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d115547, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115547, d152830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115548 q = 1) (hb : d152831 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d115548, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115548, d152831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115549 q = 1) (hb : d152832 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d115549, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115549, d152832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46457 (p : Pattern) (ha : d115555 p = 1) (hb : d152838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115550 q = 1) (hb : d152833 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d115550, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46456 q ha hb
    | true =>
      simp only [d115550, d152833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115551 q = 1) (hb : d152834 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d115551, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115551, d152834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115552 q = 1) (hb : d152835 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d115552, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115552, d152835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115553 q = 1) (hb : d152836 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d115553, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115553, d152836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115554 q = 1) (hb : d152837 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d115554, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115554, d152837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115555 q = 1) (hb : d152838 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d115555, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115555, d152838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46458 (p : Pattern) (ha : d115561 p = 1) (hb : d152844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115556 q = 1) (hb : d152839 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d115556, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46457 q ha hb
    | true =>
      simp only [d115556, d152839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115557 q = 1) (hb : d152840 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d115557, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115557, d152840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115558 q = 1) (hb : d152841 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d115558, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115558, d152841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115559 q = 1) (hb : d152842 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d115559, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115559, d152842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115560 q = 1) (hb : d152843 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d115560, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115560, d152843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115561 q = 1) (hb : d152844 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d115561, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115561, d152844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46459 (p : Pattern) (ha : d115567 p = 1) (hb : d152850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d115562 q = 1) (hb : d152845 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d115562, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46458 q ha hb
    | true =>
      simp only [d115562, d152845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d115563 q = 1) (hb : d152846 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d115563, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d115563, d152846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d115564 q = 1) (hb : d152847 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d115564, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d115564, d152847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d115565 q = 1) (hb : d152848 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d115565, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d115565, d152848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d115566 q = 1) (hb : d152849 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d115566, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d115566, d152849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d115567 q = 1) (hb : d152850 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d115567, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d115567, d152850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46460 (p : Pattern) (ha : d20893 p = 1) (hb : d116752 p = 1) : d120066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20892 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d29 q = 1) (hb : d116750 q = 1) : d29 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20893 q = 1) (hb : d116752 q = 1) : d120066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20893, d116752, d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d20893, d116752, d120066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46461 (p : Pattern) (ha : d20899 p = 1) (hb : d116753 p = 1) : d120072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20894 q = 1) (hb : d116752 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46460 q ha hb
    | true =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h2 (q : Pattern) (ha : d20895 q = 1) (hb : d116752 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20896 q = 1) (hb : d116752 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20897 q = 1) (hb : d116753 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20897, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d31 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d33 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d34 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d34, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20898 q = 1) (hb : d116753 q = 1) : d120071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20898, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20899 q = 1) (hb : d116753 q = 1) : d120072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20899, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46462 (p : Pattern) (ha : d20905 p = 1) (hb : d116753 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20904 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20904, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20905 q = 1) (hb : d116753 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46463 (p : Pattern) (ha : d116753 p = 1) (hb : d150001 p = 1) : d120084 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20906 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46462 q ha hb
    | true =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d149997 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d149997, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d149998 q = 1) : d120081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149998, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d149999 q = 1) : d120082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d149999, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150000 q = 1) : d120083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150000, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150001 q = 1) : d120084 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150001, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150001, d120084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46464 (p : Pattern) (ha : d20912 p = 1) (hb : d116753 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20904 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20904, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20912 q = 1) (hb : d116753 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20912, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46465 (p : Pattern) (ha : d116753 p = 1) (hb : d150006 p = 1) : d120091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20906 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46462 q ha hb
    | true =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d149997 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d149997, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d149998 q = 1) : d120081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d149998, d120081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d149999 q = 1) : d120082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d149999, d120082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150000 q = 1) : d120083 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150000, d120083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19782 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19783 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d20913 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46464 q ha hb
    | true =>
      simp only [d20913, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150002 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150002, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116753 q = 1) (hb : d150003 q = 1) : d120088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150003, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116753 q = 1) (hb : d150004 q = 1) : d120089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150004, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150004, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116753 q = 1) (hb : d150005 q = 1) : d120090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150005, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150005, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116753 q = 1) (hb : d150006 q = 1) : d120091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150006, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150006, d120091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro46466 (p : Pattern) (ha : d116753 p = 1) (hb : d150013 p = 1) : d120096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20913 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46464 q ha hb
    | true =>
      simp only [d20913, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150002 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150002, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150003 q = 1) : d120088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150003, d120088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150011 q = 1) : d120089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150011, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150011, d120089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150012 q = 1) : d120090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150012, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150012, d120090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150013 q = 1) : d120096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150013, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150013, d120096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46467 (p : Pattern) (ha : d20932 p = 1) (hb : d116752 p = 1) : d120102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20931 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70 q = 1) (hb : d116750 q = 1) : d70 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20932 q = 1) (hb : d116752 q = 1) : d120102 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20932, d116752, d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d20932, d116752, d120102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46468 (p : Pattern) (ha : d20938 p = 1) (hb : d116753 p = 1) : d120108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20933 q = 1) (hb : d116752 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46467 q ha hb
    | true =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h2 (q : Pattern) (ha : d20934 q = 1) (hb : d116752 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20935 q = 1) (hb : d116752 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20936 q = 1) (hb : d116753 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20936, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d72 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
    | true =>
      simp only [d72, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d73 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d75 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75, d116753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20937 q = 1) (hb : d116753 q = 1) : d120107 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20937, d120107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20938 q = 1) (hb : d116753 q = 1) : d120108 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20938, d120108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46469 (p : Pattern) (ha : d20944 p = 1) (hb : d116753 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46468 q ha hb
    | true =>
      simp only [d20939, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19769 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20941 q = 1) (hb : d116753 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20942 q = 1) (hb : d116753 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20942, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20943 q = 1) (hb : d116753 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20943, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20944 q = 1) (hb : d116753 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20944, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46470 (p : Pattern) (ha : d116753 p = 1) (hb : d150023 p = 1) : d120120 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20945 q = 1) (hb : d116753 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46469 q ha hb
    | true =>
      simp only [d20945, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19770 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150019 q = 1) : d120116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150019, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150019, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19770 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150020 q = 1) : d120117 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150020, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150020, d120117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150021 q = 1) : d120118 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150021, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150021, d120118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150022 q = 1) : d120119 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150022, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150022, d120119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150023 q = 1) : d120120 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150023, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150023, d120120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46471 (p : Pattern) (ha : d116753 p = 1) (hb : d150029 p = 1) : d120126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19773 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19773 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19774 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150007 q = 1) : d120092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150007, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46463 q ha hb
    | true =>
      simp only [d150007, d120092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46465 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19775 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150008 q = 1) : d120093 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150008, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150008, d120093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150009 q = 1) : d120094 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150009, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150009, d120094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150010 q = 1) : d120095 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150010, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150010, d120095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150014 q = 1) : d120097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150014, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150014, d120097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46466 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150015 q = 1) : d120098 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150015, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150015, d120098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150016 q = 1) : d120099 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150016, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150016, d120099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150017 q = 1) : d120100 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150017, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150017, d120100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150018 q = 1) : d120101 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150018, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150018, d120101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150024 q = 1) : d120121 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150024, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150024, d120121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46470 q ha hb
  have h17 (q : Pattern) (ha : d116753 q = 1) (hb : d150025 q = 1) : d120122 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150025, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150025, d120122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d116753 q = 1) (hb : d150026 q = 1) : d120123 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150026, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150026, d120123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d116753 q = 1) (hb : d150027 q = 1) : d120124 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150027, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150027, d120124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d116753 q = 1) (hb : d150028 q = 1) : d120125 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150028, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150028, d120125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116753 q = 1) (hb : d150029 q = 1) : d120126 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150029, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150029, d120126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro46472 (p : Pattern) (ha : d20966 p = 1) (hb : d116753 p = 1) : d120136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46462 q ha hb
    | true =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20966 q = 1) (hb : d116753 q = 1) : d120136 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d120136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46473 (p : Pattern) (ha : d20973 p = 1) (hb : d116753 p = 1) : d120143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46462 q ha hb
    | true =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20913 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46464 q ha hb
    | true =>
      simp only [d20913, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19765 q ha hb
  have h7 (q : Pattern) (ha : d20969 q = 1) (hb : d116753 q = 1) : d120139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d120139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20970 q = 1) (hb : d116753 q = 1) : d120140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20970, d120140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d20971 q = 1) (hb : d116753 q = 1) : d120141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d120141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20972 q = 1) (hb : d116753 q = 1) : d120142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d120142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d20973 q = 1) (hb : d116753 q = 1) : d120143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20973, d120143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46474 (p : Pattern) (ha : d21058 p = 1) (hb : d116753 p = 1) : d120195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20906 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46462 q ha hb
    | true =>
      simp only [d20906, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
  have h2 (q : Pattern) (ha : d20962 q = 1) (hb : d116753 q = 1) : d120132 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d120132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20963 q = 1) (hb : d116753 q = 1) : d120133 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20963, d120133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20964 q = 1) (hb : d116753 q = 1) : d120134 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d120134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20965 q = 1) (hb : d116753 q = 1) : d120135 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d120135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19763 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21058 q = 1) (hb : d116753 q = 1) : d120195 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21058, d120195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro46475 (p : Pattern) (ha : d20978 p = 1) (hb : d116753 p = 1) : d120148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20977 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20978 q = 1) (hb : d116753 q = 1) : d120148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d120148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46476 (p : Pattern) (ha : d20985 p = 1) (hb : d116753 p = 1) : d120155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20983 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20984 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20984, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d20985 q = 1) (hb : d116753 q = 1) : d120155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d120155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46477 (p : Pattern) (ha : d20996 p = 1) (hb : d116752 p = 1) : d196073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20994 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20995 q = 1) (hb : d116750 q = 1) : d20995 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20996 q = 1) (hb : d116752 q = 1) : d196073 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20996, d116752, d196073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d20996, d116752, d196073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46478 (p : Pattern) (ha : d21002 p = 1) (hb : d116753 p = 1) : d196079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d116752 q = 1) : d196074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46477 q ha hb
    | true =>
      simp only [d20997, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46460 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d116752 q = 1) : d196075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d116752 q = 1) : d196076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21000 q = 1) (hb : d116753 q = 1) : d196077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d116753, d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d116753, d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d20894 q = 1) (hb : d116752 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46460 q ha hb
    | true =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h7 (q : Pattern) (ha : d20895 q = 1) (hb : d116752 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20896 q = 1) (hb : d116752 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20897 q = 1) (hb : d116753 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20897, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21001 q = 1) (hb : d116753 q = 1) : d196078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d196078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21001, d196078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21002 q = 1) (hb : d116753 q = 1) : d196079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d196079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21002, d196079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46479 (p : Pattern) (ha : d21008 p = 1) (hb : d116753 p = 1) : d196085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46478 q ha hb
    | true =>
      simp only [d21003, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d116753 q = 1) : d196083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d116753 q = 1) : d196084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d116753 q = 1) : d196085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d196085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d196085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46480 (p : Pattern) (ha : d21029 p = 1) (hb : d116753 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d116753 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46481 (p : Pattern) (ha : d116753 p = 1) (hb : d150039 p = 1) : d196091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20979 q = 1) (hb : d116753 q = 1) : d120149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46475 q ha hb
    | true =>
      simp only [d20979, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
  have h2 (q : Pattern) (ha : d20980 q = 1) (hb : d116753 q = 1) : d120150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20981 q = 1) (hb : d116753 q = 1) : d120151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20981, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20982 q = 1) (hb : d116753 q = 1) : d120152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20986 q = 1) (hb : d116753 q = 1) : d120156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46476 q ha hb
    | true =>
      simp only [d20986, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
  have h6 (q : Pattern) (ha : d20987 q = 1) (hb : d116753 q = 1) : d120157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20988 q = 1) (hb : d116753 q = 1) : d120158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20988, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21009 q = 1) (hb : d116753 q = 1) : d196086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46479 q ha hb
    | true =>
      simp only [d21009, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46462 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150035 q = 1) : d196087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150035, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21030 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46480 q ha hb
    | true =>
      simp only [d21030, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21031 q = 1) (hb : d116753 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21031, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150036 q = 1) : d196088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150036, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150037 q = 1) : d196089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150037, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150038 q = 1) : d196090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150038, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150039 q = 1) : d196091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d196091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150039, d196091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46482 (p : Pattern) (ha : d21036 p = 1) (hb : d116753 p = 1) : d120178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20903 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20903, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20977 q = 1) (hb : d116753 q = 1) : d120147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d120147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21036 q = 1) (hb : d116753 q = 1) : d120178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21036, d120178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46483 (p : Pattern) (ha : d21041 p = 1) (hb : d116753 p = 1) : d120183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19762 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20902 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20983 q = 1) (hb : d116753 q = 1) : d120153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d120153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20984 q = 1) (hb : d116753 q = 1) : d120154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20984, d120154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21041 q = 1) (hb : d116753 q = 1) : d120183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21041, d120183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46484 (p : Pattern) (ha : d21045 p = 1) (hb : d116753 p = 1) : d196092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46478 q ha hb
    | true =>
      simp only [d21003, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d116753 q = 1) : d196083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d116753 q = 1) : d196084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d116753 q = 1) : d196092 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d196092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d196092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46485 (p : Pattern) (ha : d21050 p = 1) (hb : d116753 p = 1) : d120085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46461 q ha hb
    | true =>
      simp only [d20900, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d116753 q = 1) : d120085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d120085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46486 (p : Pattern) (ha : d116753 p = 1) (hb : d150044 p = 1) : d196098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20979 q = 1) (hb : d116753 q = 1) : d120149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46475 q ha hb
    | true =>
      simp only [d20979, d120149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19776 q ha hb
  have h2 (q : Pattern) (ha : d20980 q = 1) (hb : d116753 q = 1) : d120150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d120150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20981 q = 1) (hb : d116753 q = 1) : d120151 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20981, d120151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20982 q = 1) (hb : d116753 q = 1) : d120152 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d120152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20986 q = 1) (hb : d116753 q = 1) : d120156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46476 q ha hb
    | true =>
      simp only [d20986, d120156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19777 q ha hb
  have h6 (q : Pattern) (ha : d20987 q = 1) (hb : d116753 q = 1) : d120157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d120157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20988 q = 1) (hb : d116753 q = 1) : d120158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20988, d120158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21009 q = 1) (hb : d116753 q = 1) : d196086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46479 q ha hb
    | true =>
      simp only [d21009, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46462 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150035 q = 1) : d196087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d150035, d196087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d21030 q = 1) (hb : d116753 q = 1) : d120079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46480 q ha hb
    | true =>
      simp only [d21030, d120079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21031 q = 1) (hb : d116753 q = 1) : d120080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21031, d120080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150036 q = 1) : d196088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150036, d196088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150037 q = 1) : d196089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d150037, d196089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150038 q = 1) : d196090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150038, d196090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21037 q = 1) (hb : d116753 q = 1) : d120179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46482 q ha hb
    | true =>
      simp only [d21037, d120179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19782 q ha hb
  have h16 (q : Pattern) (ha : d21038 q = 1) (hb : d116753 q = 1) : d120180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d120180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21039 q = 1) (hb : d116753 q = 1) : d120181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21039, d120181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21040 q = 1) (hb : d116753 q = 1) : d120182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d120182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21042 q = 1) (hb : d116753 q = 1) : d120184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46483 q ha hb
    | true =>
      simp only [d21042, d120184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19783 q ha hb
  have h20 (q : Pattern) (ha : d21043 q = 1) (hb : d116753 q = 1) : d120185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d120185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21044 q = 1) (hb : d116753 q = 1) : d120186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21044, d120186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21046 q = 1) (hb : d116753 q = 1) : d196093 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46484 q ha hb
    | true =>
      simp only [d21046, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46464 q ha hb
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150040 q = 1) : d196094 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d150040, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d21051 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46485 q ha hb
    | true =>
      simp only [d21051, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21052 q = 1) (hb : d116753 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21052, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d116753 q = 1) (hb : d150041 q = 1) : d196095 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150041, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d116753 q = 1) (hb : d150042 q = 1) : d196096 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d196096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d150042, d196096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d116753 q = 1) (hb : d150043 q = 1) : d196097 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d196097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d150043, d196097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d116753 q = 1) (hb : d150044 q = 1) : d196098 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d196098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150044, d196098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro46487 (p : Pattern) (ha : d116753 p = 1) (hb : d150051 p = 1) : d196105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d116753 q = 1) : d196093 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46484 q ha hb
    | true =>
      simp only [d21046, d196093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46464 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150040 q = 1) : d196094 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150040, d196094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21051 q = 1) (hb : d116753 q = 1) : d120086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46485 q ha hb
    | true =>
      simp only [d21051, d120086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21052 q = 1) (hb : d116753 q = 1) : d120087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21052, d120087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150041 q = 1) : d196095 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150041, d196095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150049 q = 1) : d196103 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d196103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150049, d196103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150050 q = 1) : d196104 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d196104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150050, d196104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150051 q = 1) : d196105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d196105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150051, d196105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46488 (p : Pattern) (ha : d21077 p = 1) (hb : d116752 p = 1) : d196111 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d21075 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21076 q = 1) (hb : d116750 q = 1) : d21076 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21077 q = 1) (hb : d116752 q = 1) : d196111 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21077, d116752, d196111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d21077, d116752, d196111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro46489 (p : Pattern) (ha : d21083 p = 1) (hb : d116753 p = 1) : d196117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d116752 q = 1) : d196112 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46488 q ha hb
    | true =>
      simp only [d21078, d196112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46467 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d116752 q = 1) : d196113 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d196113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d116752 q = 1) : d196114 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d196114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20935 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21081 q = 1) (hb : d116753 q = 1) : d196115 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d116753, d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d116753, d196115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d20933 q = 1) (hb : d116752 q = 1) : d120103 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46467 q ha hb
    | true =>
      simp only [d20933, d120103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19768 q ha hb
  have h7 (q : Pattern) (ha : d20934 q = 1) (hb : d116752 q = 1) : d120104 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d120104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20935 q = 1) (hb : d116752 q = 1) : d120105 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d120105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d74 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20936 q = 1) (hb : d116753 q = 1) : d120106 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20936, d116753, d120106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d21082 q = 1) (hb : d116753 q = 1) : d196116 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d196116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21082, d196116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21083 q = 1) (hb : d116753 q = 1) : d196117 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d196117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21083, d196117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46490 (p : Pattern) (ha : d21089 p = 1) (hb : d116753 p = 1) : d196123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d116753 q = 1) : d196118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46489 q ha hb
    | true =>
      simp only [d21084, d196118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d116753 q = 1) : d196119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d196119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46468 q ha hb
    | true =>
      simp only [d20939, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d116753 q = 1) : d196120 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d196120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d196120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d116753 q = 1) : d196121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d196121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d196121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d116753 q = 1) : d196122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d196122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d196122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d116753 q = 1) : d196123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d196123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d196123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro46491 (p : Pattern) (ha : d21110 p = 1) (hb : d116753 p = 1) : d120114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d116753 q = 1) : d120109 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46468 q ha hb
    | true =>
      simp only [d20939, d120109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d116753 q = 1) : d120110 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d120110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21107 q = 1) (hb : d116753 q = 1) : d120111 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21107, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21107, d120111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21108 q = 1) (hb : d116753 q = 1) : d120112 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21108, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21108, d120112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21109 q = 1) (hb : d116753 q = 1) : d120113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21109, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21109, d120113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21110 q = 1) (hb : d116753 q = 1) : d120114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21110, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21110, d120114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro46492 (p : Pattern) (ha : d116753 p = 1) (hb : d150061 p = 1) : d196129 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21090 q = 1) (hb : d116753 q = 1) : d196124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21090, d196124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46490 q ha hb
    | true =>
      simp only [d21090, d196124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46469 q ha hb
  have h2 (q : Pattern) (ha : d116753 q = 1) (hb : d150057 q = 1) : d196125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d196125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d150057, d196125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d21111 q = 1) (hb : d116753 q = 1) : d120115 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21111, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46491 q ha hb
    | true =>
      simp only [d21111, d120115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21112 q = 1) (hb : d116753 q = 1) : d120116 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21112, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21112, d120116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150058 q = 1) : d196126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d196126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150058, d196126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150059 q = 1) : d196127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d196127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150059, d196127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150060 q = 1) : d196128 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d196128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150060, d196128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150061 q = 1) : d196129 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d196129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150061, d196129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46493 (p : Pattern) (ha : d116753 p = 1) (hb : d150067 p = 1) : d196135 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20967 q = 1) (hb : d116753 q = 1) : d120137 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20967, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20967, d120137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46472 q ha hb
  have h2 (q : Pattern) (ha : d20968 q = 1) (hb : d116753 q = 1) : d120138 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20968, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20968, d120138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20974 q = 1) (hb : d116753 q = 1) : d120144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46472 q ha hb
    | true =>
      simp only [d20974, d120144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46473 q ha hb
  have h4 (q : Pattern) (ha : d20975 q = 1) (hb : d116753 q = 1) : d120145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20975, d120145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20976 q = 1) (hb : d116753 q = 1) : d120146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20976, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20976, d120146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150045 q = 1) : d196099 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d196099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46481 q ha hb
    | true =>
      simp only [d150045, d196099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46486 q ha hb
  have h7 (q : Pattern) (ha : d21059 q = 1) (hb : d116753 q = 1) : d120196 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21059, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46474 q ha hb
    | true =>
      simp only [d21059, d120196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19774 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150046 q = 1) : d196100 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d196100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150046, d196100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150047 q = 1) : d196101 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d196101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150047, d196101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150048 q = 1) : d196102 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d196102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d150048, d196102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150052 q = 1) : d196106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d196106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150052, d196106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46487 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19792 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150053 q = 1) : d196107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d196107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150053, d196107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150054 q = 1) : d196108 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d196108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150054, d196108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150055 q = 1) : d196109 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d196109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150055, d196109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d116753 q = 1) (hb : d150056 q = 1) : d196110 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d196110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150056, d196110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d116753 q = 1) (hb : d150062 q = 1) : d196130 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d196130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150062, d196130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46492 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19793 q ha hb
  have h19 (q : Pattern) (ha : d116753 q = 1) (hb : d150063 q = 1) : d196131 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d196131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150063, d196131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d116753 q = 1) (hb : d150064 q = 1) : d196132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d196132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150064, d196132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d116753 q = 1) (hb : d150065 q = 1) : d196133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d196133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150065, d196133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d116753 q = 1) (hb : d150066 q = 1) : d196134 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d196134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150066, d196134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d116753 q = 1) (hb : d150067 q = 1) : d196135 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d196135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150067, d196135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro46494 (p : Pattern) (ha : d116753 p = 1) (hb : d150073 p = 1) : d196141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19772 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d116753 q = 1) (hb : d150030 q = 1) : d120127 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150030, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150030, d120127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46471 q ha hb
  have h6 (q : Pattern) (ha : d116753 q = 1) (hb : d150031 q = 1) : d120128 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150031, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150031, d120128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d116753 q = 1) (hb : d150032 q = 1) : d120129 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150032, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150032, d120129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d116753 q = 1) (hb : d150033 q = 1) : d120130 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150033, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150033, d120130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d116753 q = 1) (hb : d150034 q = 1) : d120131 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150034, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d150034, d120131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d116753 q = 1) (hb : d150068 q = 1) : d196136 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d196136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150068, d196136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46493 q ha hb
  have h11 (q : Pattern) (ha : d116753 q = 1) (hb : d150069 q = 1) : d196137 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d196137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150069, d196137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d116753 q = 1) (hb : d150070 q = 1) : d196138 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d196138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150070, d196138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d116753 q = 1) (hb : d150071 q = 1) : d196139 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d196139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150071, d196139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d116753 q = 1) (hb : d150072 q = 1) : d196140 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d196140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150072, d196140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d116753 q = 1) (hb : d150073 q = 1) : d196141 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d196141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150073, d196141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro46495 (p : Pattern) (ha : d21131 p = 1) (hb : d116753 p = 1) : d196079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d116752 q = 1) : d196074 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46477 q ha hb
    | true =>
      simp only [d20997, d196074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46460 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d116752 q = 1) : d196075 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d196075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d116752 q = 1) : d196076 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d196076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20896 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21000 q = 1) (hb : d116753 q = 1) : d196077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d116753, d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d116753, d196077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d20894 q = 1) (hb : d116752 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46460 q ha hb
    | true =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h7 (q : Pattern) (ha : d20895 q = 1) (hb : d116752 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20896 q = 1) (hb : d116752 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21129 q = 1) (hb : d116753 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21129, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21130 q = 1) (hb : d116753 q = 1) : d196078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21130, d196078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21130, d196078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21131 q = 1) (hb : d116753 q = 1) : d196079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21131, d196079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21131, d196079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro46496 (p : Pattern) (ha : d21135 p = 1) (hb : d116753 p = 1) : d120072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20894 q = 1) (hb : d116752 q = 1) : d120067 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46460 q ha hb
    | true =>
      simp only [d20894, d120067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro19761 q ha hb
  have h2 (q : Pattern) (ha : d20895 q = 1) (hb : d116752 q = 1) : d120068 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d120068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20896 q = 1) (hb : d116752 q = 1) : d120069 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d120069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21129 q = 1) (hb : d116753 q = 1) : d120070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21129, d116753, d120070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21134 q = 1) (hb : d116753 q = 1) : d120071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21134, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21134, d120071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21135 q = 1) (hb : d116753 q = 1) : d120072 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21135, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21135, d120072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro46497 (p : Pattern) (ha : d21141 p = 1) (hb : d116753 p = 1) : d196085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d116753 q = 1) : d196080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46495 q ha hb
    | true =>
      simp only [d21132, d196080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d116753 q = 1) : d196081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d196081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d116753 q = 1) : d196082 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d196082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d116753 q = 1) : d196083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d196083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d116753 q = 1) : d196084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d196084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21141 q = 1) (hb : d116753 q = 1) : d196085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21141, d196085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21141, d196085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro46498 (p : Pattern) (ha : d21145 p = 1) (hb : d116753 p = 1) : d120078 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d116753 q = 1) : d120073 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46496 q ha hb
    | true =>
      simp only [d21136, d120073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d116753 q = 1) : d120074 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d120074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d116753 q = 1) : d120075 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d120075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d116753 q = 1) : d120076 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d120076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d116753 q = 1) : d120077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d120077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21145 q = 1) (hb : d116753 q = 1) : d120078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21145, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21145, d120078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro46499 (p : Pattern) (ha : d21151 p = 1) (hb : d116753 p = 1) : d196146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d116753 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d116753 q = 1) : d196086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46497 q ha hb
    | true =>
      simp only [d21146, d196086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46498 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d116753 q = 1) : d196142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d196142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d196142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d116753 q = 1) : d196143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d196143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d196143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d116753 q = 1) : d196144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d196144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d196144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d116753 q = 1) : d196145 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d196145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d196145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21151 q = 1) (hb : d116753 q = 1) : d196146 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d196146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d196146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
