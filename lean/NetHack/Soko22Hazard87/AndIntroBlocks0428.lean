import NetHack.Soko22Hazard87.AndIntroBlocks0427
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro107000 (p : Pattern) (ha : d262219 p = 1) (hb : d321787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262087 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262165 q = 1) (hb : d320611 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262165, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106996 q ha hb
    | true =>
      simp only [d262165, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106997 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262167 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262168 q = 1) (hb : d320612 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262168, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262168, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262169 q = 1) (hb : d321769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262169, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262169, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262170 q = 1) (hb : d321770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262170, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262170, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262174 q = 1) (hb : d321772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262174, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262174, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106998 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262175 q = 1) (hb : d321773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262175, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262175, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262176 q = 1) (hb : d321774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262176, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262176, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262177 q = 1) (hb : d321775 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262177, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262177, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262178 q = 1) (hb : d321776 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262178, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262178, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262214 q = 1) (hb : d321782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262214, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262214, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106999 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262215 q = 1) (hb : d321783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262215, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262215, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262216 q = 1) (hb : d321784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262216, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262216, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262217 q = 1) (hb : d321785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262217, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262217, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262218 q = 1) (hb : d321786 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262218, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262218, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262219 q = 1) (hb : d321787 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262219, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262219, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107001 (p : Pattern) (ha : d262225 p = 1) (hb : d321793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d262068 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d262068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66694 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d262069 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d262069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d262070 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d262070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d262071 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d262071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d262072 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d262072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262220 q = 1) (hb : d321788 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262220, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262220, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107000 q ha hb
  have h8 (q : Pattern) (ha : d262221 q = 1) (hb : d321789 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262221, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262221, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262222 q = 1) (hb : d321790 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262222, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262222, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262223 q = 1) (hb : d321791 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262223, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262223, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d262224 q = 1) (hb : d321792 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262224, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262224, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d262225 q = 1) (hb : d321793 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262225, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d262225, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro107002 (p : Pattern) (ha : d262339 p = 1) (hb : d320773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262243 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106675 q ha hb
    | true =>
      simp only [d262243, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106676 q ha hb
  have h5 (q : Pattern) (ha : d262329 q = 1) (hb : d320769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262329, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262336 q = 1) (hb : d320770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262336, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262337 q = 1) (hb : d320771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262337, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262338 q = 1) (hb : d320772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262338, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262339 q = 1) (hb : d320773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262339, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262339, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107003 (p : Pattern) (ha : d262360 p = 1) (hb : d320783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262269 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262278 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262243 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262243, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106675 q ha hb
    | true =>
      simp only [d262243, d320768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106676 q ha hb
  have h4 (q : Pattern) (ha : d262329 q = 1) (hb : d320769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262329, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262329, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262335 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262336 q = 1) (hb : d320770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262336, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262336, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262337 q = 1) (hb : d320771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262337, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262337, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262338 q = 1) (hb : d320772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262338, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262338, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262345 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262350 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262253 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106678 q ha hb
    | true =>
      simp only [d262253, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106679 q ha hb
  have h13 (q : Pattern) (ha : d262353 q = 1) (hb : d320779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262353, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262357 q = 1) (hb : d320780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262357, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262358 q = 1) (hb : d320781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262358, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262358, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262359 q = 1) (hb : d320782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262359, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262359, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262360 q = 1) (hb : d320783 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262360, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262360, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107004 (p : Pattern) (ha : d262380 p = 1) (hb : d321796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262253 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262253, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106678 q ha hb
    | true =>
      simp only [d262253, d320778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106679 q ha hb
  have h3 (q : Pattern) (ha : d262353 q = 1) (hb : d320779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262353, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262353, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262356 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262357 q = 1) (hb : d320780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262357, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262357, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262378 q = 1) (hb : d320781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262378, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262378, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262379 q = 1) (hb : d320782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262379, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262379, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262380 q = 1) (hb : d321796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262380, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262380, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107005 (p : Pattern) (ha : d262448 p = 1) (hb : d321807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262437 q = 1) (hb : d321802 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262437, d321802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106712 q ha hb
    | true =>
      simp only [d262437, d321802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106715 q ha hb
  have h3 (q : Pattern) (ha : d262438 q = 1) (hb : d321803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262438, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262438, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262444 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262445 q = 1) (hb : d321804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262445, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262445, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262446 q = 1) (hb : d321805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262446, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262446, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262447 q = 1) (hb : d321806 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262447, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262447, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262448 q = 1) (hb : d321807 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262448, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262448, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107006 (p : Pattern) (ha : d262461 p = 1) (hb : d321813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262261 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262361 q = 1) (hb : d320784 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262361, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107002 q ha hb
    | true =>
      simp only [d262361, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107003 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262374 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262375 q = 1) (hb : d320785 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262375, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262375, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262376 q = 1) (hb : d321794 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262376, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262376, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262377 q = 1) (hb : d321795 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262377, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262377, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262381 q = 1) (hb : d321797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262381, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262381, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107004 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262383 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262384 q = 1) (hb : d321798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262384, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262384, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262385 q = 1) (hb : d321799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262385, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262385, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262386 q = 1) (hb : d321800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262386, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262386, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262387 q = 1) (hb : d321801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262387, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262387, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262449 q = 1) (hb : d321808 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262449, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262449, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107005 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262456 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262457 q = 1) (hb : d321809 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262457, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262457, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262458 q = 1) (hb : d321810 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262458, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262458, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262459 q = 1) (hb : d321811 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262459, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262459, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262460 q = 1) (hb : d321812 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262460, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262460, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262461 q = 1) (hb : d321813 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262461, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262461, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107007 (p : Pattern) (ha : d262467 p = 1) (hb : d321819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262462 q = 1) (hb : d321814 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262462, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262462, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107006 q ha hb
  have h2 (q : Pattern) (ha : d262463 q = 1) (hb : d321815 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262463, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262463, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262464 q = 1) (hb : d321816 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262464, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262464, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262465 q = 1) (hb : d321817 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262465, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262465, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262466 q = 1) (hb : d321818 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262466, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262466, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262467 q = 1) (hb : d321819 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262467, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262467, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107008 (p : Pattern) (ha : d262607 p = 1) (hb : d321028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262504 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106725 q ha hb
    | true =>
      simp only [d262504, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106726 q ha hb
  have h5 (q : Pattern) (ha : d262597 q = 1) (hb : d321024 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262597, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262604 q = 1) (hb : d321025 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262604, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262605 q = 1) (hb : d321026 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262605, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262606 q = 1) (hb : d321027 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262606, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262607 q = 1) (hb : d321028 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262607, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262607, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107009 (p : Pattern) (ha : d262628 p = 1) (hb : d321038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262530 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262596 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262504 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262504, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106725 q ha hb
    | true =>
      simp only [d262504, d321023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106726 q ha hb
  have h4 (q : Pattern) (ha : d262597 q = 1) (hb : d321024 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262597, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262597, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262603 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262604 q = 1) (hb : d321025 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262604, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262604, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262605 q = 1) (hb : d321026 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262605, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262605, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262606 q = 1) (hb : d321027 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262606, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262606, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262613 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262618 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262514 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106728 q ha hb
    | true =>
      simp only [d262514, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106729 q ha hb
  have h13 (q : Pattern) (ha : d262621 q = 1) (hb : d321034 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262621, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262625 q = 1) (hb : d321035 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262625, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262626 q = 1) (hb : d321036 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262626, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262626, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262627 q = 1) (hb : d321037 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262627, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262627, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262628 q = 1) (hb : d321038 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262628, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262628, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107010 (p : Pattern) (ha : d262648 p = 1) (hb : d321823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262620 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262514 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262514, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106728 q ha hb
    | true =>
      simp only [d262514, d321033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106729 q ha hb
  have h3 (q : Pattern) (ha : d262621 q = 1) (hb : d321034 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262621, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262621, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262624 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262625 q = 1) (hb : d321035 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262625, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262625, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262646 q = 1) (hb : d321036 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262646, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262646, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262647 q = 1) (hb : d321037 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262647, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262647, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262648 q = 1) (hb : d321823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262648, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262648, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107011 (p : Pattern) (ha : d262733 p = 1) (hb : d321834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262722 q = 1) (hb : d321829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262722, d321829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106766 q ha hb
    | true =>
      simp only [d262722, d321829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106769 q ha hb
  have h3 (q : Pattern) (ha : d262723 q = 1) (hb : d321830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262723, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262723, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262729 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262730 q = 1) (hb : d321831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262730, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262730, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262731 q = 1) (hb : d321832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262731, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262731, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262732 q = 1) (hb : d321833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262732, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262732, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262733 q = 1) (hb : d321834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262733, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262733, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107012 (p : Pattern) (ha : d262746 p = 1) (hb : d321840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262522 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262629 q = 1) (hb : d321039 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262629, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107008 q ha hb
    | true =>
      simp only [d262629, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107009 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262642 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262643 q = 1) (hb : d321040 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262643, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d262643, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262644 q = 1) (hb : d321821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262644, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262644, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d262645 q = 1) (hb : d321822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262645, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262645, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d262649 q = 1) (hb : d321824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262649, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262649, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107010 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d262651 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d262652 q = 1) (hb : d321825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262652, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d262652, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d262653 q = 1) (hb : d321826 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262653, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d262653, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d262654 q = 1) (hb : d321827 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262654, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d262654, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d262655 q = 1) (hb : d321828 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262655, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d262655, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d262734 q = 1) (hb : d321835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262734, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d262734, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107011 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262741 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262742 q = 1) (hb : d321836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d262742, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262742, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262743 q = 1) (hb : d321837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d262743, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d262743, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d262744 q = 1) (hb : d321838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d262744, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d262744, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d262745 q = 1) (hb : d321839 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d262745, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d262745, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d262746 q = 1) (hb : d321840 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d262746, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d262746, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107013 (p : Pattern) (ha : d262752 p = 1) (hb : d321846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262747 q = 1) (hb : d321841 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d262747, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262747, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107012 q ha hb
  have h2 (q : Pattern) (ha : d262748 q = 1) (hb : d321842 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d262748, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262748, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d262749 q = 1) (hb : d321843 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d262749, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262749, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d262750 q = 1) (hb : d321844 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d262750, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262750, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d262751 q = 1) (hb : d321845 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d262751, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262751, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d262752 q = 1) (hb : d321846 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d262752, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262752, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107014 (p : Pattern) (ha : d262965 p = 1) (hb : d321361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d262846 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106784 q ha hb
    | true =>
      simp only [d262846, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106785 q ha hb
  have h5 (q : Pattern) (ha : d262946 q = 1) (hb : d321357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d262946, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d262962 q = 1) (hb : d321358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d262962, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d262963 q = 1) (hb : d321359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262963, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d262964 q = 1) (hb : d321360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262964, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d262965 q = 1) (hb : d321361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262965, d321361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262965, d321361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107015 (p : Pattern) (ha : d262986 p = 1) (hb : d321371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262881 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d262945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d262846 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262846, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106784 q ha hb
    | true =>
      simp only [d262846, d321356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106785 q ha hb
  have h4 (q : Pattern) (ha : d262946 q = 1) (hb : d321357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262946, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d262946, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d262961 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d262962 q = 1) (hb : d321358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262962, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d262962, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d262963 q = 1) (hb : d321359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262963, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262963, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d262964 q = 1) (hb : d321360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262964, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d262964, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d262971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d262976 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d262856 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106787 q ha hb
    | true =>
      simp only [d262856, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106788 q ha hb
  have h13 (q : Pattern) (ha : d262979 q = 1) (hb : d321367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d262979, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d262983 q = 1) (hb : d321368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d262983, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d262984 q = 1) (hb : d321369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d262984, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d262984, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d262985 q = 1) (hb : d321370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d262985, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d262985, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d262986 q = 1) (hb : d321371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d262986, d321371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d262986, d321371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107016 (p : Pattern) (ha : d263006 p = 1) (hb : d321851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d262978 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262856 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d262856, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106787 q ha hb
    | true =>
      simp only [d262856, d321366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106788 q ha hb
  have h3 (q : Pattern) (ha : d262979 q = 1) (hb : d321367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d262979, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262979, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d262982 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d262983 q = 1) (hb : d321368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d262983, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d262983, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263004 q = 1) (hb : d321369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263004, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263004, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263005 q = 1) (hb : d321370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263005, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263005, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263006 q = 1) (hb : d321851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263006, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263006, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107017 (p : Pattern) (ha : d263127 p = 1) (hb : d321862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263102 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263107 q = 1) (hb : d321857 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263107, d321857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106826 q ha hb
    | true =>
      simp only [d263107, d321857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106831 q ha hb
  have h3 (q : Pattern) (ha : d263108 q = 1) (hb : d321858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263108, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263108, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263123 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263124 q = 1) (hb : d321859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263124, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263124, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263125 q = 1) (hb : d321860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263125, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263125, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263126 q = 1) (hb : d321861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263126, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263126, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263127 q = 1) (hb : d321862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263127, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263127, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107018 (p : Pattern) (ha : d263140 p = 1) (hb : d321868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d262864 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d262987 q = 1) (hb : d321372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d262987, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107014 q ha hb
    | true =>
      simp only [d262987, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107015 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d263001 q = 1) (hb : d321373 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263001, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d263001, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263002 q = 1) (hb : d321849 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263002, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263002, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263003 q = 1) (hb : d321850 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263003, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263003, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263007 q = 1) (hb : d321852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263007, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263007, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107016 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263009 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263010 q = 1) (hb : d321853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263010, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263010, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263011 q = 1) (hb : d321854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263011, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263011, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263012 q = 1) (hb : d321855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263012, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263012, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263013 q = 1) (hb : d321856 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263013, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263013, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263128 q = 1) (hb : d321863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263128, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263128, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107017 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263135 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263136 q = 1) (hb : d321864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263136, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263136, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263137 q = 1) (hb : d321865 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263137, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263137, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263138 q = 1) (hb : d321866 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263138, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263138, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263139 q = 1) (hb : d321867 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263139, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263139, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263140 q = 1) (hb : d321868 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263140, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263140, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107019 (p : Pattern) (ha : d263146 p = 1) (hb : d321874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263141 q = 1) (hb : d321869 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263141, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263141, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107018 q ha hb
  have h2 (q : Pattern) (ha : d263142 q = 1) (hb : d321870 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263142, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263142, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263143 q = 1) (hb : d321871 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263143, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263143, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263144 q = 1) (hb : d321872 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263144, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263144, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263145 q = 1) (hb : d321873 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263145, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263145, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263146 q = 1) (hb : d321874 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263146, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263146, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107020 (p : Pattern) (ha : d46527 p = 1) (hb : d263364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46522 q = 1) (hb : d263250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d263250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106845 q ha hb
    | true =>
      simp only [d46522, d263250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106846 q ha hb
  have h5 (q : Pattern) (ha : d46523 q = 1) (hb : d263332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d263332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46523, d263332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46524 q = 1) (hb : d263361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d263361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46524, d263361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46525 q = 1) (hb : d263362 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d263362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46525, d263362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46526 q = 1) (hb : d263363 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d263363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46526, d263363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46527 q = 1) (hb : d263364 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d263364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, d263364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107021 (p : Pattern) (ha : d46537 p = 1) (hb : d263385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263285 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263331 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46522 q = 1) (hb : d263250 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, d263250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106845 q ha hb
    | true =>
      simp only [d46522, d263250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106846 q ha hb
  have h4 (q : Pattern) (ha : d46523 q = 1) (hb : d263332 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d263332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46523, d263332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263360 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46524 q = 1) (hb : d263361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d263361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46524, d263361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46525 q = 1) (hb : d263362 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d263362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46525, d263362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46526 q = 1) (hb : d263363 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d263363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d263363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263375 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d46532 q = 1) (hb : d263260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d263260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106848 q ha hb
    | true =>
      simp only [d46532, d263260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106849 q ha hb
  have h13 (q : Pattern) (ha : d46533 q = 1) (hb : d263378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d263378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46533, d263378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46534 q = 1) (hb : d263382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d263382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46534, d263382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46535 q = 1) (hb : d263383 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d263383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46535, d263383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46536 q = 1) (hb : d263384 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d263384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46536, d263384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46537 q = 1) (hb : d263385 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d263385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46537, d263385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107022 (p : Pattern) (ha : d263405 p = 1) (hb : d321880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46532 q = 1) (hb : d263260 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, d263260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106848 q ha hb
    | true =>
      simp only [d46532, d263260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106849 q ha hb
  have h3 (q : Pattern) (ha : d46533 q = 1) (hb : d263378 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d263378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46533, d263378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263381 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46534 q = 1) (hb : d263382 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d263382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46534, d263382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46535 q = 1) (hb : d263403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d263403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d263403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46536 q = 1) (hb : d263404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d263404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d263404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263405 q = 1) (hb : d321880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263405, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263405, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro107023 (p : Pattern) (ha : d263537 p = 1) (hb : d321891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263506 q = 1) (hb : d321886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263506, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106889 q hb ha
    | true =>
      simp only [d263506, d321886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106857 q hb ha
  have h3 (q : Pattern) (ha : d263507 q = 1) (hb : d321887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263507, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263507, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263533 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263534 q = 1) (hb : d321888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263534, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263534, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263535 q = 1) (hb : d321889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263535, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263535, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263536 q = 1) (hb : d321890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263536, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263536, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263537 q = 1) (hb : d321891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263537, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263537, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107024 (p : Pattern) (ha : d263550 p = 1) (hb : d321897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263268 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d263386 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d263386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107020 q ha hb
    | true =>
      simp only [d46538, d263386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107021 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263399 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46539 q = 1) (hb : d263400 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d263400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d263400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263401 q = 1) (hb : d321878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263401, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263401, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263402 q = 1) (hb : d321879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263402, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263402, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263406 q = 1) (hb : d321881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263406, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263406, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107022 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263408 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263409 q = 1) (hb : d321882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263409, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263409, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263410 q = 1) (hb : d321883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263410, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263410, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263411 q = 1) (hb : d321884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263411, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263411, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263412 q = 1) (hb : d321885 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263412, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263412, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263538 q = 1) (hb : d321892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263538, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263538, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107023 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263545 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263546 q = 1) (hb : d321893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263546, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263546, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263547 q = 1) (hb : d321894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263547, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263547, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263548 q = 1) (hb : d321895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263548, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263548, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263549 q = 1) (hb : d321896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263549, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263549, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263550 q = 1) (hb : d321897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263550, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263550, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107025 (p : Pattern) (ha : d263556 p = 1) (hb : d321903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263551 q = 1) (hb : d321898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263551, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263551, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107024 q ha hb
  have h2 (q : Pattern) (ha : d263552 q = 1) (hb : d321899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263552, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263552, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263553 q = 1) (hb : d321900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263553, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263553, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263554 q = 1) (hb : d321901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263554, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263554, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263555 q = 1) (hb : d321902 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263555, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263555, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263556 q = 1) (hb : d321903 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263556, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263556, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107026 (p : Pattern) (ha : d46921 p = 1) (hb : d263768 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46916 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106907 q ha hb
    | true =>
      simp only [d46916, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106908 q ha hb
  have h5 (q : Pattern) (ha : d46917 q = 1) (hb : d263728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46917, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46918 q = 1) (hb : d263765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46918, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46919 q = 1) (hb : d263766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46919, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46920 q = 1) (hb : d263767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46920, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46921 q = 1) (hb : d263768 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d263768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d263768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107027 (p : Pattern) (ha : d46931 p = 1) (hb : d263790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263690 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263699 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46916 q = 1) (hb : d263664 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106907 q ha hb
    | true =>
      simp only [d46916, d263664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106908 q ha hb
  have h4 (q : Pattern) (ha : d46917 q = 1) (hb : d263728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46917, d263728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d263764 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46918 q = 1) (hb : d263765 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46918, d263765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46919 q = 1) (hb : d263766 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46919, d263766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46920 q = 1) (hb : d263767 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d263767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d263774 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d263779 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d46926 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106910 q ha hb
    | true =>
      simp only [d46926, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106911 q ha hb
  have h13 (q : Pattern) (ha : d46927 q = 1) (hb : d263783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46927, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46928 q = 1) (hb : d263787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46928, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46929 q = 1) (hb : d263788 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d263788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46929, d263788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46930 q = 1) (hb : d263789 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d263789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46930, d263789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46931 q = 1) (hb : d263790 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d263790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46931, d263790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107028 (p : Pattern) (ha : d263815 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d46926 q = 1) (hb : d263674 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106910 q ha hb
    | true =>
      simp only [d46926, d263674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106911 q ha hb
  have h3 (q : Pattern) (ha : d46927 q = 1) (hb : d263783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46927, d263783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263786 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46928 q = 1) (hb : d263787 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46928, d263787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46929 q = 1) (hb : d263813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d263813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d263813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46930 q = 1) (hb : d263814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d263814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d263814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263815 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263815, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263815, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro107029 (p : Pattern) (ha : d47117 p = 1) (hb : d263905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47097 q = 1) (hb : d263863 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47097, d263863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106943 q ha hb
    | true =>
      simp only [d47097, d263863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106918 q ha hb
  have h2 (q : Pattern) (ha : d47098 q = 1) (hb : d263864 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47098, d263864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47098, d263864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47099 q = 1) (hb : d263865 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47099, d263865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47099, d263865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d47107 q = 1) (hb : d263872 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d263872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106918 q ha hb
    | true =>
      simp only [d47107, d263872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106945 q ha hb
  have h5 (q : Pattern) (ha : d47108 q = 1) (hb : d263873 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d263873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d263873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47109 q = 1) (hb : d263874 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d263874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d263874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d47110 q = 1) (hb : d263875 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47110, d263875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47110, d263875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d47107 q = 1) (hb : d263891 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, d263891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106918 q ha hb
    | true =>
      simp only [d47107, d263891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106919 q ha hb
  have h9 (q : Pattern) (ha : d47108 q = 1) (hb : d263892 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, d263892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47108, d263892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d47109 q = 1) (hb : d263893 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, d263893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47109, d263893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d47115 q = 1) (hb : d263894 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, d263894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47115, d263894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d47116 q = 1) (hb : d263904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47116, d263904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47116, d263904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d47117 q = 1) (hb : d263905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47117, d263905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47117, d263905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro107030 (p : Pattern) (ha : d47131 p = 1) (hb : d263911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47118 q = 1) (hb : d263906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47118, d263906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107029 q ha hb
    | true =>
      simp only [d47118, d263906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d47119 q = 1) (hb : d263907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47119, d263907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47119, d263907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d47126 q = 1) (hb : d263897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, d263897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106920 q ha hb
    | true =>
      simp only [d47126, d263897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d47127 q = 1) (hb : d263898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, d263898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47127, d263898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d47128 q = 1) (hb : d263908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47128, d263908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47128, d263908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47129 q = 1) (hb : d263909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47129, d263909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47129, d263909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47130 q = 1) (hb : d263910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47130, d263910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47130, d263910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47131 q = 1) (hb : d263911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47131, d263911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47131, d263911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro107031 (p : Pattern) (ha : d263922 p = 1) (hb : d321921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53337 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263917 q = 1) (hb : d321916 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d263917, d321916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro89556 q hb ha
    | true =>
      simp only [d263917, d321916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q hb ha
  have h2 (q : Pattern) (ha : d263918 q = 1) (hb : d321917 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d263918, d321917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263918, d321917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d263919 q = 1) (hb : d321918 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d263919, d321918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263919, d321918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d101726 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46871 q = 1) (hb : d101727 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104283 q ha hb
    | true =>
      simp only [d46871, d101727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h7 (q : Pattern) (ha : d46872 q = 1) (hb : d101728 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46872, d101728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46873 q = 1) (hb : d101729 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46873, d101729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d263920 q = 1) (hb : d321919 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d263920, d321919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263920, d321919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263921 q = 1) (hb : d321920 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d263921, d321920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263921, d321920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h11 (q : Pattern) (ha : d263922 q = 1) (hb : d321921 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d263922, d321921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263922, d321921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h11 p ha hb
theorem andIntro107032 (p : Pattern) (ha : d263928 p = 1) (hb : d321927 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d47086 q = 1) (hb : d263857 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, d263857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47086, d263857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106899 q ha hb
  have h2 (q : Pattern) (ha : d46877 q = 1) (hb : d263616 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, d263616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106899 q ha hb
    | true =>
      simp only [d46877, d263616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d47087 q = 1) (hb : d263858 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, d263858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, d263858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d46878 q = 1) (hb : d263617 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, d263617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, d263617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d47088 q = 1) (hb : d263859 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, d263859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, d263859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d47089 q = 1) (hb : d263860 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, d263860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, d263860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d47095 q = 1) (hb : d263889 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, d263889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, d263889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d47101 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d47101, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106902 q ha hb
  have h9 (q : Pattern) (ha : d46889 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106902 q ha hb
    | true =>
      simp only [d46889, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d47102 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263923 q = 1) (hb : d321922 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d263923, d321922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107031 q ha hb
    | true =>
      simp only [d263923, d321922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d263924 q = 1) (hb : d321923 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d263924, d321923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d263924, d321923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d263925 q = 1) (hb : d321924 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d263925, d321924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d263925, d321924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263926 q = 1) (hb : d321925 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d263926, d321925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263926, d321925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d263927 q = 1) (hb : d321926 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d263927, d321926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d263927, d321926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d263928 q = 1) (hb : d321927 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d263928, d321927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d263928, d321927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro107033 (p : Pattern) (ha : d263934 p = 1) (hb : d321933 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263929 q = 1) (hb : d321928 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d263929, d321928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106918 q hb ha
    | true =>
      simp only [d263929, d321928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107032 q ha hb
  have h2 (q : Pattern) (ha : d263930 q = 1) (hb : d321929 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d263930, d321929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263930, d321929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263931 q = 1) (hb : d321930 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d263931, d321930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263931, d321930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263932 q = 1) (hb : d321931 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d263932, d321931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263932, d321931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263933 q = 1) (hb : d321932 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d263933, d321932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263933, d321932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263934 q = 1) (hb : d321933 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d263934, d321933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263934, d321933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107034 (p : Pattern) (ha : d263940 p = 1) (hb : d321939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263935 q = 1) (hb : d321934 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d263935, d321934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107033 q ha hb
    | true =>
      simp only [d263935, d321934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d263936 q = 1) (hb : d321935 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d263936, d321935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263936, d321935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263937 q = 1) (hb : d321936 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d263937, d321936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d263937, d321936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d263938 q = 1) (hb : d321937 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d263938, d321937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263938, d321937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d263939 q = 1) (hb : d321938 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d263939, d321938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d263939, d321938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d263940 q = 1) (hb : d321939 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d263940, d321939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d263940, d321939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107035 (p : Pattern) (ha : d263972 p = 1) (hb : d321945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d263903 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d263941 q = 1) (hb : d321940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263941, d321940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107030 q hb ha
    | true =>
      simp only [d263941, d321940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107034 q ha hb
  have h3 (q : Pattern) (ha : d263942 q = 1) (hb : d321941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d263942, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263942, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d263968 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263969 q = 1) (hb : d321942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d263969, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263969, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263970 q = 1) (hb : d321943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d263970, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263970, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263971 q = 1) (hb : d321944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d263971, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263971, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d263972 q = 1) (hb : d321945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d263972, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263972, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107036 (p : Pattern) (ha : d263989 p = 1) (hb : d321951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d263682 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d263791 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d263791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107026 q ha hb
    | true =>
      simp only [d46932, d263791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107027 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d263809 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d263810 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d263810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d263810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d263811 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263811, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d263811, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d263812 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263812, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263812, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263816 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263816, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263816, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107028 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d263818 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d263819 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263819, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d263819, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d263820 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263820, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d263820, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d263821 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263821, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d263821, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d263822 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263822, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263822, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263973 q = 1) (hb : d321946 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d263973, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d263973, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107035 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d263984 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d263985 q = 1) (hb : d321947 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d263985, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d263985, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d263986 q = 1) (hb : d321948 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d263986, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d263986, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d263987 q = 1) (hb : d321949 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d263987, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d263987, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d263988 q = 1) (hb : d321950 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d263988, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d263988, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d263989 q = 1) (hb : d321951 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d263989, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d263989, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107037 (p : Pattern) (ha : d263995 p = 1) (hb : d321957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d263990 q = 1) (hb : d321952 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d263990, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263990, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107036 q ha hb
  have h2 (q : Pattern) (ha : d263991 q = 1) (hb : d321953 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d263991, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263991, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d263992 q = 1) (hb : d321954 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d263992, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263992, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263993 q = 1) (hb : d321955 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d263993, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263993, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d263994 q = 1) (hb : d321956 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d263994, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263994, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263995 q = 1) (hb : d321957 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d263995, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d263995, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107038 (p : Pattern) (ha : d264001 p = 1) (hb : d321963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d262468 q = 1) (hb : d321820 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262468, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107001 q ha hb
    | true =>
      simp only [d262468, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107007 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d262753 q = 1) (hb : d321847 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d262753, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d262753, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107013 q ha hb
  have h3 (q : Pattern) (ha : d262754 q = 1) (hb : d321848 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d262754, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d262754, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d263147 q = 1) (hb : d321875 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263147, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263147, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107019 q ha hb
  have h5 (q : Pattern) (ha : d263148 q = 1) (hb : d321876 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263148, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263148, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d263149 q = 1) (hb : d321877 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263149, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d263149, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d263557 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263557, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263557, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107025 q ha hb
  have h8 (q : Pattern) (ha : d263558 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263558, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263558, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d263559 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263559, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263559, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d263560 q = 1) (hb : d321907 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263560, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d263560, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d263996 q = 1) (hb : d321958 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d263996, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263996, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107037 q ha hb
  have h12 (q : Pattern) (ha : d263997 q = 1) (hb : d321959 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d263997, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263997, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d263998 q = 1) (hb : d321960 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d263998, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263998, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d263999 q = 1) (hb : d321961 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d263999, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d263999, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d264000 q = 1) (hb : d321962 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d264000, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d264000, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d264001 q = 1) (hb : d321963 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d264001, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d264001, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro107039 (p : Pattern) (ha : d264007 p = 1) (hb : d321969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264002 q = 1) (hb : d321964 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d264002, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107038 q ha hb
    | true =>
      simp only [d264002, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264003 q = 1) (hb : d321965 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d264003, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264003, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264004 q = 1) (hb : d321966 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d264004, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264004, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264005 q = 1) (hb : d321967 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d264005, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264005, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264006 q = 1) (hb : d321968 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d264006, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264006, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264007 q = 1) (hb : d321969 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d264007, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264007, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107040 (p : Pattern) (ha : d264013 p = 1) (hb : d321975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264008 q = 1) (hb : d321970 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d264008, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107039 q ha hb
    | true =>
      simp only [d264008, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264009 q = 1) (hb : d321971 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d264009, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264009, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264010 q = 1) (hb : d321972 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d264010, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264010, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264011 q = 1) (hb : d321973 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d264011, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264011, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264012 q = 1) (hb : d321974 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d264012, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264012, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264013 q = 1) (hb : d321975 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d264013, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264013, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107041 (p : Pattern) (ha : d264019 p = 1) (hb : d321981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264014 q = 1) (hb : d321976 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d264014, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107040 q ha hb
    | true =>
      simp only [d264014, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264015 q = 1) (hb : d321977 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d264015, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264015, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264016 q = 1) (hb : d321978 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d264016, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264016, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264017 q = 1) (hb : d321979 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d264017, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264017, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264018 q = 1) (hb : d321980 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d264018, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264018, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264019 q = 1) (hb : d321981 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d264019, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264019, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107042 (p : Pattern) (ha : d264025 p = 1) (hb : d321987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264020 q = 1) (hb : d321982 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d264020, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107041 q ha hb
    | true =>
      simp only [d264020, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264021 q = 1) (hb : d321983 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d264021, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264021, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264022 q = 1) (hb : d321984 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d264022, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264022, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264023 q = 1) (hb : d321985 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d264023, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264023, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264024 q = 1) (hb : d321986 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d264024, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264024, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264025 q = 1) (hb : d321987 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d264025, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264025, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107043 (p : Pattern) (ha : d264031 p = 1) (hb : d321993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264026 q = 1) (hb : d321988 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d264026, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107042 q ha hb
    | true =>
      simp only [d264026, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264027 q = 1) (hb : d321989 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d264027, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264027, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264028 q = 1) (hb : d321990 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d264028, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264028, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264029 q = 1) (hb : d321991 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d264029, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264029, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264030 q = 1) (hb : d321992 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d264030, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264030, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264031 q = 1) (hb : d321993 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d264031, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264031, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107044 (p : Pattern) (ha : d264037 p = 1) (hb : d321999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264032 q = 1) (hb : d321994 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d264032, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107043 q ha hb
    | true =>
      simp only [d264032, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264033 q = 1) (hb : d321995 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d264033, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264033, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264034 q = 1) (hb : d321996 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d264034, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264034, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264035 q = 1) (hb : d321997 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d264035, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264035, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264036 q = 1) (hb : d321998 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d264036, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264036, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264037 q = 1) (hb : d321999 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d264037, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264037, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107045 (p : Pattern) (ha : d264043 p = 1) (hb : d322005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d264038 q = 1) (hb : d322000 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d264038, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107044 q ha hb
    | true =>
      simp only [d264038, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d264039 q = 1) (hb : d322001 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d264039, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d264039, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d264040 q = 1) (hb : d322002 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d264040, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d264040, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d264041 q = 1) (hb : d322003 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d264041, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d264041, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d264042 q = 1) (hb : d322004 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d264042, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d264042, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d264043 q = 1) (hb : d322005 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d264043, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d264043, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107046 (p : Pattern) (ha : d265953 p = 1) (hb : d320603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320539 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265949 q = 1) (hb : d320599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265949, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265950 q = 1) (hb : d320600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265950, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265951 q = 1) (hb : d320601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265951, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265952 q = 1) (hb : d320602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265952, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265953 q = 1) (hb : d320603 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265953, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265953, d320603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107047 (p : Pattern) (ha : d265958 p = 1) (hb : d320610 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33360 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d320539 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265949 q = 1) (hb : d320599 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265949, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265949, d320599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33394 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265950 q = 1) (hb : d320600 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265950, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265950, d320600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265951 q = 1) (hb : d320601 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265951, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265951, d320601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265952 q = 1) (hb : d320602 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265952, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265952, d320602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33403 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33407 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d320546 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265954 q = 1) (hb : d320606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265954, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265955 q = 1) (hb : d320607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265955, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265956 q = 1) (hb : d320608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265956, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265956, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265957 q = 1) (hb : d320609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265957, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265957, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265958 q = 1) (hb : d320610 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265958, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265958, d320610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107048 (p : Pattern) (ha : d265965 p = 1) (hb : d321771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320546 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265954 q = 1) (hb : d320606 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265954, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265954, d320606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33415 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265955 q = 1) (hb : d320607 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265955, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265955, d320607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265963 q = 1) (hb : d320608 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265963, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265963, d320608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265964 q = 1) (hb : d320609 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265964, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265964, d320609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265965 q = 1) (hb : d321771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265965, d321771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265965, d321771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107049 (p : Pattern) (ha : d265975 p = 1) (hb : d321781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320582 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265971 q = 1) (hb : d321777 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265971, d321777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265971, d321777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265972 q = 1) (hb : d321778 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265972, d321778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265972, d321778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d265973 q = 1) (hb : d321779 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265973, d321779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265973, d321779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265974 q = 1) (hb : d321780 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265974, d321780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265974, d321780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265975 q = 1) (hb : d321781 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265975, d321781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265975, d321781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107050 (p : Pattern) (ha : d265981 p = 1) (hb : d321787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265959 q = 1) (hb : d320611 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265959, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107046 q ha hb
    | true =>
      simp only [d265959, d320611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107047 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265960 q = 1) (hb : d320612 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265960, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265960, d320612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265961 q = 1) (hb : d321769 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265961, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265961, d321769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d265962 q = 1) (hb : d321770 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265962, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265962, d321770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265966 q = 1) (hb : d321772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265966, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265966, d321772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107048 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d265967 q = 1) (hb : d321773 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265967, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d265967, d321773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d265968 q = 1) (hb : d321774 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265968, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d265968, d321774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d265969 q = 1) (hb : d321775 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265969, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d265969, d321775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d265970 q = 1) (hb : d321776 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265970, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d265970, d321776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d265976 q = 1) (hb : d321782 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265976, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265976, d321782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107049 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265977 q = 1) (hb : d321783 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265977, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265977, d321783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265978 q = 1) (hb : d321784 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d265978, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d265978, d321784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d265979 q = 1) (hb : d321785 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d265979, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d265979, d321785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d265980 q = 1) (hb : d321786 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d265980, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d265980, d321786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d265981 q = 1) (hb : d321787 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d265981, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d265981, d321787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107051 (p : Pattern) (ha : d265987 p = 1) (hb : d321793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d265944 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d265944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66749 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d265945 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d265945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d265946 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d265946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d265947 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d265947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d265948 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d265948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d265982 q = 1) (hb : d321788 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d265982, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265982, d321788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107050 q ha hb
  have h8 (q : Pattern) (ha : d265983 q = 1) (hb : d321789 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d265983, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265983, d321789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265984 q = 1) (hb : d321790 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d265984, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265984, d321790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265985 q = 1) (hb : d321791 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d265985, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265985, d321791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d265986 q = 1) (hb : d321792 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d265986, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265986, d321792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d265987 q = 1) (hb : d321793 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d265987, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d265987, d321793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro107052 (p : Pattern) (ha : d265992 p = 1) (hb : d320773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265988 q = 1) (hb : d320769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d265988, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d265989 q = 1) (hb : d320770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d265989, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d265990 q = 1) (hb : d320771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265990, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d265991 q = 1) (hb : d320772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265991, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d265992 q = 1) (hb : d320773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265992, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d265992, d320773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107053 (p : Pattern) (ha : d265997 p = 1) (hb : d320783 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33543 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d320768 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d265988 q = 1) (hb : d320769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265988, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d265988, d320769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d33653 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d265989 q = 1) (hb : d320770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265989, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d265989, d320770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d265990 q = 1) (hb : d320771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265990, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265990, d320771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d265991 q = 1) (hb : d320772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265991, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d265991, d320772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d33663 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d33668 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d265993 q = 1) (hb : d320779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d265993, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d265994 q = 1) (hb : d320780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d265994, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d265995 q = 1) (hb : d320781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d265995, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d265995, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d265996 q = 1) (hb : d320782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d265996, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d265996, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d265997 q = 1) (hb : d320783 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d265997, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d265997, d320783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107054 (p : Pattern) (ha : d266004 p = 1) (hb : d321796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33670 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d320778 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265993 q = 1) (hb : d320779 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d265993, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d265993, d320779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33677 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d265994 q = 1) (hb : d320780 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d265994, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d265994, d320780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266002 q = 1) (hb : d320781 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266002, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266002, d320781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266003 q = 1) (hb : d320782 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266003, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266003, d320782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266004 q = 1) (hb : d321796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266004, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266004, d321796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107055 (p : Pattern) (ha : d266014 p = 1) (hb : d321807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33753 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321802 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266010 q = 1) (hb : d321803 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266010, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266010, d321803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d33793 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266011 q = 1) (hb : d321804 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266011, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266011, d321804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266012 q = 1) (hb : d321805 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266012, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266012, d321805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266013 q = 1) (hb : d321806 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266013, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266013, d321806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266014 q = 1) (hb : d321807 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266014, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266014, d321807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107056 (p : Pattern) (ha : d266020 p = 1) (hb : d321813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33535 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d265998 q = 1) (hb : d320784 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d265998, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107052 q ha hb
    | true =>
      simp only [d265998, d320784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107053 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33695 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d265999 q = 1) (hb : d320785 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d265999, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d265999, d320785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266000 q = 1) (hb : d321794 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266000, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266000, d321794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266001 q = 1) (hb : d321795 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266001, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266001, d321795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266005 q = 1) (hb : d321797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266005, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266005, d321797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107054 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d33704 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266006 q = 1) (hb : d321798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266006, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266006, d321798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266007 q = 1) (hb : d321799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266007, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266007, d321799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266008 q = 1) (hb : d321800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266008, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266008, d321800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266009 q = 1) (hb : d321801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266009, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266009, d321801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266015 q = 1) (hb : d321808 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266015, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266015, d321808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107055 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d33809 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266016 q = 1) (hb : d321809 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266016, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266016, d321809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266017 q = 1) (hb : d321810 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266017, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266017, d321810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266018 q = 1) (hb : d321811 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266018, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266018, d321811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266019 q = 1) (hb : d321812 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266019, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266019, d321812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266020 q = 1) (hb : d321813 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266020, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266020, d321813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107057 (p : Pattern) (ha : d266026 p = 1) (hb : d321819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266021 q = 1) (hb : d321814 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266021, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266021, d321814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107056 q ha hb
  have h2 (q : Pattern) (ha : d266022 q = 1) (hb : d321815 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266022, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266022, d321815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266023 q = 1) (hb : d321816 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266023, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266023, d321816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266024 q = 1) (hb : d321817 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266024, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266024, d321817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266025 q = 1) (hb : d321818 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266025, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266025, d321818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266026 q = 1) (hb : d321819 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266026, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266026, d321819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107058 (p : Pattern) (ha : d266032 p = 1) (hb : d321028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266028 q = 1) (hb : d321024 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266028, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266029 q = 1) (hb : d321025 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266029, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266030 q = 1) (hb : d321026 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266030, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266031 q = 1) (hb : d321027 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266031, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266032 q = 1) (hb : d321028 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266032, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266032, d321028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107059 (p : Pattern) (ha : d266037 p = 1) (hb : d321038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33883 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d33892 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d33949 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d321023 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266028 q = 1) (hb : d321024 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266028, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266028, d321024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34023 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266029 q = 1) (hb : d321025 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266029, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266029, d321025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266030 q = 1) (hb : d321026 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266030, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266030, d321026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266031 q = 1) (hb : d321027 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266031, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266031, d321027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34033 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34038 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266033 q = 1) (hb : d321034 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266033, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266034 q = 1) (hb : d321035 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266034, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266035 q = 1) (hb : d321036 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266035, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266035, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266036 q = 1) (hb : d321037 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266036, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266036, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266037 q = 1) (hb : d321038 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266037, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266037, d321038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107060 (p : Pattern) (ha : d266044 p = 1) (hb : d321823 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321033 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266033 q = 1) (hb : d321034 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266033, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266033, d321034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34047 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266034 q = 1) (hb : d321035 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266034, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266034, d321035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266042 q = 1) (hb : d321036 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266042, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266042, d321036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266043 q = 1) (hb : d321037 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266043, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266043, d321037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266044 q = 1) (hb : d321823 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266044, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266044, d321823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107061 (p : Pattern) (ha : d266054 p = 1) (hb : d321834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321829 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266050 q = 1) (hb : d321830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266050, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266050, d321830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34195 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266051 q = 1) (hb : d321831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266051, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266051, d321831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266052 q = 1) (hb : d321832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266052, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266052, d321832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266053 q = 1) (hb : d321833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266053, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266053, d321833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266054 q = 1) (hb : d321834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266054, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266054, d321834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107062 (p : Pattern) (ha : d266060 p = 1) (hb : d321840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d33875 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266038 q = 1) (hb : d321039 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266038, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107058 q ha hb
    | true =>
      simp only [d266038, d321039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107059 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34065 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266039 q = 1) (hb : d321040 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266039, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266039, d321040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266040 q = 1) (hb : d321821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266040, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266040, d321821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266041 q = 1) (hb : d321822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266041, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266041, d321822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266045 q = 1) (hb : d321824 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266045, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266045, d321824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107060 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34074 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266046 q = 1) (hb : d321825 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266046, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266046, d321825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266047 q = 1) (hb : d321826 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266047, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266047, d321826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266048 q = 1) (hb : d321827 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266048, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266048, d321827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266049 q = 1) (hb : d321828 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266049, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266049, d321828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266055 q = 1) (hb : d321835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266055, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266055, d321835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107061 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34211 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266056 q = 1) (hb : d321836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266056, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266056, d321836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266057 q = 1) (hb : d321837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266057, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266057, d321837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266058 q = 1) (hb : d321838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266058, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266058, d321838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266059 q = 1) (hb : d321839 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266059, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266059, d321839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266060 q = 1) (hb : d321840 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266060, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266060, d321840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107063 (p : Pattern) (ha : d266066 p = 1) (hb : d321846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266061 q = 1) (hb : d321841 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266061, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266061, d321841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107062 q ha hb
  have h2 (q : Pattern) (ha : d266062 q = 1) (hb : d321842 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266062, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266062, d321842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266063 q = 1) (hb : d321843 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266063, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266063, d321843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266064 q = 1) (hb : d321844 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266064, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266064, d321844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266065 q = 1) (hb : d321845 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266065, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266065, d321845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266066 q = 1) (hb : d321846 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266066, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266066, d321846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107064 (p : Pattern) (ha : d266073 p = 1) (hb : d321361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266069 q = 1) (hb : d321357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266069, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d266070 q = 1) (hb : d321358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266070, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d266071 q = 1) (hb : d321359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266071, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266072 q = 1) (hb : d321360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266072, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266073 q = 1) (hb : d321361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266073, d321361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266073, d321361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107065 (p : Pattern) (ha : d266078 p = 1) (hb : d321371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34342 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34351 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34415 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d321356 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d266069 q = 1) (hb : d321357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266069, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d266069, d321357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d34534 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d266070 q = 1) (hb : d321358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266070, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266070, d321358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d266071 q = 1) (hb : d321359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266071, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266071, d321359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266072 q = 1) (hb : d321360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266072, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266072, d321360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d34544 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d34549 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d266074 q = 1) (hb : d321367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d266074, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266075 q = 1) (hb : d321368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266075, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266076 q = 1) (hb : d321369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266076, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d266076, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d266077 q = 1) (hb : d321370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266077, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d266077, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d266078 q = 1) (hb : d321371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266078, d321371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d266078, d321371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107066 (p : Pattern) (ha : d266085 p = 1) (hb : d321851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34551 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321366 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266074 q = 1) (hb : d321367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266074, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266074, d321367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34558 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266075 q = 1) (hb : d321368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266075, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266075, d321368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266083 q = 1) (hb : d321369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266083, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266083, d321369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266084 q = 1) (hb : d321370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266084, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266084, d321370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266085 q = 1) (hb : d321851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266085, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266085, d321851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107067 (p : Pattern) (ha : d266095 p = 1) (hb : d321862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321857 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266091 q = 1) (hb : d321858 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266091, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266091, d321858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d34751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266092 q = 1) (hb : d321859 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266092, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266092, d321859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266093 q = 1) (hb : d321860 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266093, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266093, d321860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266094 q = 1) (hb : d321861 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266094, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266094, d321861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266095 q = 1) (hb : d321862 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266095, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266095, d321862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107068 (p : Pattern) (ha : d266101 p = 1) (hb : d321868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34334 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266079 q = 1) (hb : d321372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266079, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107064 q ha hb
    | true =>
      simp only [d266079, d321372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107065 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266080 q = 1) (hb : d321373 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266080, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266080, d321373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266081 q = 1) (hb : d321849 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266081, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266081, d321849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266082 q = 1) (hb : d321850 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266082, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266082, d321850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266086 q = 1) (hb : d321852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266086, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266086, d321852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107066 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d34585 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266087 q = 1) (hb : d321853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266087, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266087, d321853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266088 q = 1) (hb : d321854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266088, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266088, d321854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266089 q = 1) (hb : d321855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266089, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266089, d321855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266090 q = 1) (hb : d321856 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266090, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266090, d321856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266096 q = 1) (hb : d321863 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266096, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266096, d321863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107067 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d34767 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266097 q = 1) (hb : d321864 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266097, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266097, d321864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266098 q = 1) (hb : d321865 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266098, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266098, d321865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266099 q = 1) (hb : d321866 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266099, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266099, d321866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266100 q = 1) (hb : d321867 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266100, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266100, d321867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266101 q = 1) (hb : d321868 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266101, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266101, d321868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107069 (p : Pattern) (ha : d266107 p = 1) (hb : d321874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266102 q = 1) (hb : d321869 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266102, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266102, d321869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107068 q ha hb
  have h2 (q : Pattern) (ha : d266103 q = 1) (hb : d321870 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266103, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266103, d321870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266104 q = 1) (hb : d321871 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266104, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266104, d321871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266105 q = 1) (hb : d321872 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266105, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266105, d321872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266106 q = 1) (hb : d321873 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266106, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266106, d321873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266107 q = 1) (hb : d321874 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266107, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266107, d321874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107070 (p : Pattern) (ha : d46527 p = 1) (hb : d266115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46523 q = 1) (hb : d266111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d266111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46523, d266111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46524 q = 1) (hb : d266112 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d266112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46524, d266112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46525 q = 1) (hb : d266113 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d266113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46525, d266113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46526 q = 1) (hb : d266114 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d266114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46526, d266114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46527 q = 1) (hb : d266115 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, d266115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46527, d266115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107071 (p : Pattern) (ha : d46537 p = 1) (hb : d266120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34908 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d34917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d34963 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46523 q = 1) (hb : d266111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, d266111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46523, d266111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35102 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46524 q = 1) (hb : d266112 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, d266112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46524, d266112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46525 q = 1) (hb : d266113 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, d266113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46525, d266113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46526 q = 1) (hb : d266114 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, d266114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46526, d266114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35112 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35117 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46532 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46533 q = 1) (hb : d266116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d266116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46533, d266116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46534 q = 1) (hb : d266117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d266117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46534, d266117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46535 q = 1) (hb : d266118 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d266118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46535, d266118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46536 q = 1) (hb : d266119 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d266119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46536, d266119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46537 q = 1) (hb : d266120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, d266120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46537, d266120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107072 (p : Pattern) (ha : d266127 p = 1) (hb : d321880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35119 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46532 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46533 q = 1) (hb : d266116 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, d266116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46533, d266116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35126 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46534 q = 1) (hb : d266117 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, d266117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46534, d266117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46535 q = 1) (hb : d266125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, d266125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46535, d266125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46536 q = 1) (hb : d266126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, d266126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46536, d266126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266127 q = 1) (hb : d321880 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266127, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266127, d321880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro107073 (p : Pattern) (ha : d266137 p = 1) (hb : d321891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321886 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266133 q = 1) (hb : d321887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266133, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266133, d321887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35330 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266134 q = 1) (hb : d321888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266134, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266134, d321888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266135 q = 1) (hb : d321889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266135, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266135, d321889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266136 q = 1) (hb : d321890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266136, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266136, d321890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266137 q = 1) (hb : d321891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266137, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266137, d321891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107074 (p : Pattern) (ha : d266143 p = 1) (hb : d321897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d34900 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46538 q = 1) (hb : d266121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, d266121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107070 q ha hb
    | true =>
      simp only [d46538, d266121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107071 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46539 q = 1) (hb : d266122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, d266122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46539, d266122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266123 q = 1) (hb : d321878 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266123, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266123, d321878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266124 q = 1) (hb : d321879 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266124, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266124, d321879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266128 q = 1) (hb : d321881 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266128, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266128, d321881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107072 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35153 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266129 q = 1) (hb : d321882 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266129, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266129, d321882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266130 q = 1) (hb : d321883 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266130, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266130, d321883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266131 q = 1) (hb : d321884 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266131, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266131, d321884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266132 q = 1) (hb : d321885 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266132, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266132, d321885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266138 q = 1) (hb : d321892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266138, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266138, d321892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107073 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35346 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266139 q = 1) (hb : d321893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266139, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266139, d321893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266140 q = 1) (hb : d321894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266140, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266140, d321894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266141 q = 1) (hb : d321895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266141, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266141, d321895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266142 q = 1) (hb : d321896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266142, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266142, d321896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266143 q = 1) (hb : d321897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266143, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266143, d321897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107075 (p : Pattern) (ha : d266149 p = 1) (hb : d321903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266144 q = 1) (hb : d321898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266144, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266144, d321898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107074 q ha hb
  have h2 (q : Pattern) (ha : d266145 q = 1) (hb : d321899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266145, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266145, d321899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266146 q = 1) (hb : d321900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266146, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266146, d321900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266147 q = 1) (hb : d321901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266147, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266147, d321901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266148 q = 1) (hb : d321902 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266148, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266148, d321902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266149 q = 1) (hb : d321903 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266149, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266149, d321903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107076 (p : Pattern) (ha : d46921 p = 1) (hb : d266158 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46917 q = 1) (hb : d266154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46917, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d46918 q = 1) (hb : d266155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46918, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46919 q = 1) (hb : d266156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46919, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d46920 q = 1) (hb : d266157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46920, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d46921 q = 1) (hb : d266158 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, d266158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46921, d266158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro107077 (p : Pattern) (ha : d46931 p = 1) (hb : d266163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35491 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35500 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35528 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d46917 q = 1) (hb : d266154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46917, d266154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d35669 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d46918 q = 1) (hb : d266155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46918, d266155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46919 q = 1) (hb : d266156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46919, d266156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d46920 q = 1) (hb : d266157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46920, d266157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d35679 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d35684 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d46927 q = 1) (hb : d266159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46927, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d46928 q = 1) (hb : d266160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46928, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d46929 q = 1) (hb : d266161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d266161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46929, d266161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d46930 q = 1) (hb : d266162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d266162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46930, d266162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d46931 q = 1) (hb : d266163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, d266163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46931, d266163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro107078 (p : Pattern) (ha : d266170 p = 1) (hb : d321910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46927 q = 1) (hb : d266159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46927, d266159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35694 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d46928 q = 1) (hb : d266160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46928, d266160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d46929 q = 1) (hb : d266168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, d266168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46929, d266168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d46930 q = 1) (hb : d266169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, d266169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d46930, d266169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266170 q = 1) (hb : d321910 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266170, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266170, d321910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro107079 (p : Pattern) (ha : d266180 p = 1) (hb : d321945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d35811 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d321940 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d266176 q = 1) (hb : d321941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d266176, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d266176, d321941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d35929 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266177 q = 1) (hb : d321942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d266177, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266177, d321942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d266178 q = 1) (hb : d321943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d266178, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266178, d321943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266179 q = 1) (hb : d321944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d266179, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266179, d321944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d266180 q = 1) (hb : d321945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d266180, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266180, d321945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107080 (p : Pattern) (ha : d266186 p = 1) (hb : d321951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d35483 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d46932 q = 1) (hb : d266164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46932, d266164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107076 q ha hb
    | true =>
      simp only [d46932, d266164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107077 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d35717 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d46933 q = 1) (hb : d266165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46933, d266165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46933, d266165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d266166 q = 1) (hb : d321908 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266166, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d266166, d321908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266167 q = 1) (hb : d321909 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266167, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d266167, d321909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266171 q = 1) (hb : d321911 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266171, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266171, d321911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107078 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d35726 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d266172 q = 1) (hb : d321912 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266172, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d266172, d321912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d266173 q = 1) (hb : d321913 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266173, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d266173, d321913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d266174 q = 1) (hb : d321914 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266174, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266174, d321914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d266175 q = 1) (hb : d321915 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266175, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266175, d321915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266181 q = 1) (hb : d321946 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d266181, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266181, d321946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107079 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d35945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d266182 q = 1) (hb : d321947 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d266182, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d266182, d321947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d266183 q = 1) (hb : d321948 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d266183, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266183, d321948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d266184 q = 1) (hb : d321949 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d266184, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d266184, d321949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d266185 q = 1) (hb : d321950 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d266185, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d266185, d321950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d266186 q = 1) (hb : d321951 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d266186, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d266186, d321951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro107081 (p : Pattern) (ha : d266192 p = 1) (hb : d321957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266187 q = 1) (hb : d321952 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d266187, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266187, d321952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107080 q ha hb
  have h2 (q : Pattern) (ha : d266188 q = 1) (hb : d321953 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d266188, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266188, d321953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d266189 q = 1) (hb : d321954 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d266189, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266189, d321954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266190 q = 1) (hb : d321955 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d266190, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266190, d321955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d266191 q = 1) (hb : d321956 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d266191, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266191, d321956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266192 q = 1) (hb : d321957 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d266192, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266192, d321957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107082 (p : Pattern) (ha : d266198 p = 1) (hb : d321963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d266027 q = 1) (hb : d321820 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266027, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107051 q ha hb
    | true =>
      simp only [d266027, d321820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107057 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d266067 q = 1) (hb : d321847 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266067, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266067, d321847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107063 q ha hb
  have h3 (q : Pattern) (ha : d266068 q = 1) (hb : d321848 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266068, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d266068, d321848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d266108 q = 1) (hb : d321875 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266108, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266108, d321875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107069 q ha hb
  have h5 (q : Pattern) (ha : d266109 q = 1) (hb : d321876 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266109, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266109, d321876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d266110 q = 1) (hb : d321877 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266110, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266110, d321877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d266150 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266150, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266150, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107075 q ha hb
  have h8 (q : Pattern) (ha : d266151 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266151, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266151, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d266152 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266152, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266152, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d266153 q = 1) (hb : d321907 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266153, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d266153, d321907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d266193 q = 1) (hb : d321958 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d266193, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266193, d321958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107081 q ha hb
  have h12 (q : Pattern) (ha : d266194 q = 1) (hb : d321959 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d266194, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266194, d321959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d266195 q = 1) (hb : d321960 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d266195, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266195, d321960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d266196 q = 1) (hb : d321961 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d266196, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266196, d321961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d266197 q = 1) (hb : d321962 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d266197, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d266197, d321962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d266198 q = 1) (hb : d321963 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d266198, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d266198, d321963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro107083 (p : Pattern) (ha : d266204 p = 1) (hb : d321969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266199 q = 1) (hb : d321964 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d266199, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107082 q ha hb
    | true =>
      simp only [d266199, d321964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266200 q = 1) (hb : d321965 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d266200, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266200, d321965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266201 q = 1) (hb : d321966 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d266201, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266201, d321966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266202 q = 1) (hb : d321967 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d266202, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266202, d321967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266203 q = 1) (hb : d321968 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d266203, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266203, d321968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266204 q = 1) (hb : d321969 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d266204, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266204, d321969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107084 (p : Pattern) (ha : d266210 p = 1) (hb : d321975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266205 q = 1) (hb : d321970 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d266205, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107083 q ha hb
    | true =>
      simp only [d266205, d321970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266206 q = 1) (hb : d321971 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d266206, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266206, d321971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266207 q = 1) (hb : d321972 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d266207, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266207, d321972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266208 q = 1) (hb : d321973 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d266208, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266208, d321973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266209 q = 1) (hb : d321974 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d266209, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266209, d321974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266210 q = 1) (hb : d321975 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d266210, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266210, d321975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107085 (p : Pattern) (ha : d266216 p = 1) (hb : d321981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266211 q = 1) (hb : d321976 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d266211, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107084 q ha hb
    | true =>
      simp only [d266211, d321976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266212 q = 1) (hb : d321977 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d266212, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266212, d321977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266213 q = 1) (hb : d321978 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d266213, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266213, d321978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266214 q = 1) (hb : d321979 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d266214, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266214, d321979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266215 q = 1) (hb : d321980 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d266215, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266215, d321980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266216 q = 1) (hb : d321981 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d266216, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266216, d321981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107086 (p : Pattern) (ha : d266222 p = 1) (hb : d321987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266217 q = 1) (hb : d321982 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d266217, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107085 q ha hb
    | true =>
      simp only [d266217, d321982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266218 q = 1) (hb : d321983 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d266218, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266218, d321983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266219 q = 1) (hb : d321984 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d266219, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266219, d321984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266220 q = 1) (hb : d321985 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d266220, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266220, d321985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266221 q = 1) (hb : d321986 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d266221, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266221, d321986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266222 q = 1) (hb : d321987 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d266222, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266222, d321987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107087 (p : Pattern) (ha : d266228 p = 1) (hb : d321993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266223 q = 1) (hb : d321988 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d266223, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107086 q ha hb
    | true =>
      simp only [d266223, d321988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266224 q = 1) (hb : d321989 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d266224, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266224, d321989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266225 q = 1) (hb : d321990 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d266225, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266225, d321990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266226 q = 1) (hb : d321991 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d266226, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266226, d321991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266227 q = 1) (hb : d321992 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d266227, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266227, d321992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266228 q = 1) (hb : d321993 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d266228, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266228, d321993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107088 (p : Pattern) (ha : d266234 p = 1) (hb : d321999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266229 q = 1) (hb : d321994 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d266229, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107087 q ha hb
    | true =>
      simp only [d266229, d321994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266230 q = 1) (hb : d321995 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d266230, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266230, d321995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266231 q = 1) (hb : d321996 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d266231, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266231, d321996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266232 q = 1) (hb : d321997 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d266232, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266232, d321997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266233 q = 1) (hb : d321998 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d266233, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266233, d321998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266234 q = 1) (hb : d321999 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d266234, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266234, d321999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107089 (p : Pattern) (ha : d266240 p = 1) (hb : d322005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d266235 q = 1) (hb : d322000 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d266235, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107088 q ha hb
    | true =>
      simp only [d266235, d322000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d266236 q = 1) (hb : d322001 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d266236, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d266236, d322001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d266237 q = 1) (hb : d322002 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d266237, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d266237, d322002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d266238 q = 1) (hb : d322003 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d266238, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d266238, d322003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d266239 q = 1) (hb : d322004 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d266239, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d266239, d322004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d266240 q = 1) (hb : d322005 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d266240, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d266240, d322005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107090 (p : Pattern) (ha : d322208 p = 1) (hb : d363221 p = 1) : d375642 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d322206 q = 1) : d322206 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d321724 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322207 q = 1) (hb : d363221 q = 1) : d375641 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d322207, d363221, d375641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322207, d363221, d375641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d363221 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322208 q = 1) (hb : d363221 q = 1) : d375642 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d322208, d375642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322208, d375642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro107091 (p : Pattern) (ha : d322214 p = 1) (hb : d363221 p = 1) : d375648 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322209 q = 1) (hb : d363221 q = 1) : d375643 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d322209, d375643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107090 q ha hb
    | true =>
      simp only [d322209, d375643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322210 q = 1) (hb : d363221 q = 1) : d375644 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d322210, d375644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322210, d375644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322211 q = 1) (hb : d363221 q = 1) : d375645 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d322211, d375645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322211, d375645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322212 q = 1) (hb : d363221 q = 1) : d375646 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d322212, d375646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322212, d375646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322213 q = 1) (hb : d363221 q = 1) : d375647 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d322213, d375647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322213, d375647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322214 q = 1) (hb : d363221 q = 1) : d375648 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d322214, d375648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322214, d375648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107092 (p : Pattern) (ha : d322220 p = 1) (hb : d375596 p = 1) : d375654 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322215 q = 1) (hb : d363221 q = 1) : d375649 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d322215, d375649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107091 q ha hb
    | true =>
      simp only [d322215, d375649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322216 q = 1) (hb : d363221 q = 1) : d375650 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d322216, d375650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322216, d375650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322217 q = 1) (hb : d363221 q = 1) : d375651 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d322217, d375651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322217, d375651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d322218 q = 1) (hb : d375595 q = 1) : d375652 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d322218, d375595, d375652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322218, d375595, d375652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322219 q = 1) (hb : d375596 q = 1) : d375653 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d375596, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322219, d375596, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d322220 q = 1) (hb : d375596 q = 1) : d375654 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322220, d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107093 (p : Pattern) (ha : d322226 p = 1) (hb : d375596 p = 1) : d375660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d375596 q = 1) : d375655 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107092 q ha hb
    | true =>
      simp only [d322221, d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d375596 q = 1) : d375656 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d375596 q = 1) : d375657 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d375596 q = 1) : d375658 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d375596 q = 1) : d375659 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d375596 q = 1) : d375660 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107094 (p : Pattern) (ha : d322232 p = 1) (hb : d375596 p = 1) : d375666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d375596 q = 1) : d375661 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107093 q ha hb
    | true =>
      simp only [d322227, d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d375596 q = 1) : d375662 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d375596 q = 1) : d375663 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d375596 q = 1) : d375664 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d375596 q = 1) : d375665 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d375596 q = 1) : d375666 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107095 (p : Pattern) (ha : d322238 p = 1) (hb : d375596 p = 1) : d375672 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d375596 q = 1) : d375667 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107094 q ha hb
    | true =>
      simp only [d322233, d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d375596 q = 1) : d375668 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d375596 q = 1) : d375669 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d375596 q = 1) : d375670 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d375596 q = 1) : d375671 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d375596 q = 1) : d375672 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107096 (p : Pattern) (ha : d322244 p = 1) (hb : d375596 p = 1) : d375678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d375596 q = 1) : d375673 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107095 q ha hb
    | true =>
      simp only [d322239, d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d375596 q = 1) : d375674 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d375596 q = 1) : d375675 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d375596 q = 1) : d375676 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d375596 q = 1) : d375677 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d375596 q = 1) : d375678 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107097 (p : Pattern) (ha : d322250 p = 1) (hb : d375596 p = 1) : d375684 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d375596 q = 1) : d375679 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107096 q ha hb
    | true =>
      simp only [d322245, d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d375596 q = 1) : d375680 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d375596 q = 1) : d375681 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d375596 q = 1) : d375682 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d375596 q = 1) : d375683 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d375596 q = 1) : d375684 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107098 (p : Pattern) (ha : d375598 p = 1) (hb : d375642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d322122 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro104963 q ha hb
    | true =>
      simp only [d319211, d322122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105010 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d322162 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d322162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105062 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d322163 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d322163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d322203 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d322203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105123 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d322204 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d322204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d322205 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d322205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321678 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86233 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321679 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321680 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d322206 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d322206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d375597 q = 1) (hb : d375641 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375597, d375641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d375597, d375641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d375598 q = 1) (hb : d375642 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375598, d375642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d375598, d375642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro107099 (p : Pattern) (ha : d375604 p = 1) (hb : d375648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375599 q = 1) (hb : d375643 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375599, d375643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107098 q ha hb
    | true =>
      simp only [d375599, d375643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375600 q = 1) (hb : d375644 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375600, d375644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375600, d375644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375601 q = 1) (hb : d375645 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375601, d375645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375601, d375645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375602 q = 1) (hb : d375646 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375602, d375646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375602, d375646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375603 q = 1) (hb : d375647 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375603, d375647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375603, d375647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375604 q = 1) (hb : d375648 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375604, d375648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375604, d375648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107100 (p : Pattern) (ha : d375610 p = 1) (hb : d375654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375605 q = 1) (hb : d375649 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375605, d375649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107099 q ha hb
    | true =>
      simp only [d375605, d375649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375606 q = 1) (hb : d375650 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375606, d375650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375606, d375650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375607 q = 1) (hb : d375651 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375607, d375651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375607, d375651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375608 q = 1) (hb : d375652 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375608, d375652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375608, d375652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375609 q = 1) (hb : d375653 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375609, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375609, d375653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375610 q = 1) (hb : d375654 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375610, d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375610, d375654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107101 (p : Pattern) (ha : d375616 p = 1) (hb : d375660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375611 q = 1) (hb : d375655 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375611, d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107100 q ha hb
    | true =>
      simp only [d375611, d375655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375612 q = 1) (hb : d375656 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375612, d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375612, d375656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375613 q = 1) (hb : d375657 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375613, d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375613, d375657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375614 q = 1) (hb : d375658 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375614, d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375614, d375658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375615 q = 1) (hb : d375659 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375615, d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375615, d375659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375616 q = 1) (hb : d375660 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375616, d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375616, d375660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107102 (p : Pattern) (ha : d375622 p = 1) (hb : d375666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375617 q = 1) (hb : d375661 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375617, d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107101 q ha hb
    | true =>
      simp only [d375617, d375661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375618 q = 1) (hb : d375662 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375618, d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375618, d375662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375619 q = 1) (hb : d375663 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375619, d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375619, d375663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375620 q = 1) (hb : d375664 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375620, d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375620, d375664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375621 q = 1) (hb : d375665 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375621, d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375621, d375665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375622 q = 1) (hb : d375666 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375622, d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375622, d375666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107103 (p : Pattern) (ha : d375628 p = 1) (hb : d375672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375623 q = 1) (hb : d375667 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375623, d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107102 q ha hb
    | true =>
      simp only [d375623, d375667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375624 q = 1) (hb : d375668 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375624, d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375624, d375668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375625 q = 1) (hb : d375669 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375625, d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375625, d375669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375626 q = 1) (hb : d375670 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375626, d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375626, d375670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375627 q = 1) (hb : d375671 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375627, d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375627, d375671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375628 q = 1) (hb : d375672 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375628, d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375628, d375672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107104 (p : Pattern) (ha : d375634 p = 1) (hb : d375678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375629 q = 1) (hb : d375673 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375629, d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107103 q ha hb
    | true =>
      simp only [d375629, d375673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375630 q = 1) (hb : d375674 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375630, d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375630, d375674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375631 q = 1) (hb : d375675 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375631, d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375631, d375675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375632 q = 1) (hb : d375676 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375632, d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375632, d375676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375633 q = 1) (hb : d375677 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375633, d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375633, d375677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375634 q = 1) (hb : d375678 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375634, d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375634, d375678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107105 (p : Pattern) (ha : d375640 p = 1) (hb : d375684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375635 q = 1) (hb : d375679 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375635, d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107104 q ha hb
    | true =>
      simp only [d375635, d375679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375636 q = 1) (hb : d375680 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375636, d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375636, d375680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375637 q = 1) (hb : d375681 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375637, d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375637, d375681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375638 q = 1) (hb : d375682 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375638, d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375638, d375682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375639 q = 1) (hb : d375683 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375639, d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375639, d375683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375640 q = 1) (hb : d375684 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375640, d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375640, d375684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107106 (p : Pattern) (ha : d363221 p = 1) (hb : d367712 p = 1) : d375686 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d367710 q = 1) : d367710 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d326621 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d363221 q = 1) (hb : d367711 q = 1) : d375685 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d363221, d367711, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d363221, d367711, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d363221 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d363221 q = 1) (hb : d367712 q = 1) : d375686 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d367712, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367712, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro107107 (p : Pattern) (ha : d363221 p = 1) (hb : d367718 p = 1) : d375692 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363221 q = 1) (hb : d367713 q = 1) : d375687 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d367713, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107106 q ha hb
    | true =>
      simp only [d367713, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363221 q = 1) (hb : d367714 q = 1) : d375688 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d367714, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367714, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363221 q = 1) (hb : d367715 q = 1) : d375689 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d367715, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367715, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d363221 q = 1) (hb : d367716 q = 1) : d375690 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d367716, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367716, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d363221 q = 1) (hb : d367717 q = 1) : d375691 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d367717, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367717, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d363221 q = 1) (hb : d367718 q = 1) : d375692 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d367718, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367718, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107108 (p : Pattern) (ha : d367724 p = 1) (hb : d375596 p = 1) : d375698 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d363221 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d363221 q = 1) (hb : d367719 q = 1) : d375693 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d367719, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107107 q ha hb
    | true =>
      simp only [d367719, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d363221 q = 1) (hb : d367720 q = 1) : d375694 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d367720, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367720, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d363221 q = 1) (hb : d367721 q = 1) : d375695 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d367721, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367721, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d367722 q = 1) (hb : d375595 q = 1) : d375696 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d375595, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d367722, d375595, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d367723 q = 1) (hb : d375596 q = 1) : d375697 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d375596, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367723, d375596, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d367724 q = 1) (hb : d375596 q = 1) : d375698 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d367724, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107109 (p : Pattern) (ha : d367730 p = 1) (hb : d375596 p = 1) : d375704 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367725 q = 1) (hb : d375596 q = 1) : d375699 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107108 q ha hb
    | true =>
      simp only [d367725, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367726 q = 1) (hb : d375596 q = 1) : d375700 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367727 q = 1) (hb : d375596 q = 1) : d375701 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367728 q = 1) (hb : d375596 q = 1) : d375702 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367729 q = 1) (hb : d375596 q = 1) : d375703 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367730 q = 1) (hb : d375596 q = 1) : d375704 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107110 (p : Pattern) (ha : d367736 p = 1) (hb : d375596 p = 1) : d375710 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367731 q = 1) (hb : d375596 q = 1) : d375705 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107109 q ha hb
    | true =>
      simp only [d367731, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367732 q = 1) (hb : d375596 q = 1) : d375706 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367733 q = 1) (hb : d375596 q = 1) : d375707 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367734 q = 1) (hb : d375596 q = 1) : d375708 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367735 q = 1) (hb : d375596 q = 1) : d375709 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367736 q = 1) (hb : d375596 q = 1) : d375710 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107111 (p : Pattern) (ha : d367742 p = 1) (hb : d375596 p = 1) : d375716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367737 q = 1) (hb : d375596 q = 1) : d375711 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107110 q ha hb
    | true =>
      simp only [d367737, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367738 q = 1) (hb : d375596 q = 1) : d375712 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367739 q = 1) (hb : d375596 q = 1) : d375713 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367740 q = 1) (hb : d375596 q = 1) : d375714 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367741 q = 1) (hb : d375596 q = 1) : d375715 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367742 q = 1) (hb : d375596 q = 1) : d375716 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107112 (p : Pattern) (ha : d367748 p = 1) (hb : d375596 p = 1) : d375722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367743 q = 1) (hb : d375596 q = 1) : d375717 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107111 q ha hb
    | true =>
      simp only [d367743, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367744 q = 1) (hb : d375596 q = 1) : d375718 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367745 q = 1) (hb : d375596 q = 1) : d375719 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367746 q = 1) (hb : d375596 q = 1) : d375720 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367747 q = 1) (hb : d375596 q = 1) : d375721 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367748 q = 1) (hb : d375596 q = 1) : d375722 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107113 (p : Pattern) (ha : d367754 p = 1) (hb : d375596 p = 1) : d375728 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375596 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367749 q = 1) (hb : d375596 q = 1) : d375723 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107112 q ha hb
    | true =>
      simp only [d367749, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367750 q = 1) (hb : d375596 q = 1) : d375724 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367751 q = 1) (hb : d375596 q = 1) : d375725 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367752 q = 1) (hb : d375596 q = 1) : d375726 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367753 q = 1) (hb : d375596 q = 1) : d375727 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367754 q = 1) (hb : d375596 q = 1) : d375728 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107114 (p : Pattern) (ha : d375598 p = 1) (hb : d375686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d319211 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105138 q ha hb
    | true =>
      simp only [d319211, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105144 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d319500 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319500, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105150 q ha hb
  have h3 (q : Pattern) (ha : d319501 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d319501, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d319887 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319887, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105156 q ha hb
  have h5 (q : Pattern) (ha : d319888 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d319888, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d319889 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d319889, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d320181 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320181, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86365 q ha hb
  have h8 (q : Pattern) (ha : d320182 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320182, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d320183 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d320183, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d320184 q = 1) (hb : d367710 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d320184, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d320184, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d375597 q = 1) (hb : d375685 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375597, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d375597, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h12 (q : Pattern) (ha : d375598 q = 1) (hb : d375686 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375598, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d375598, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h12 p ha hb
theorem andIntro107115 (p : Pattern) (ha : d375604 p = 1) (hb : d375692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375599 q = 1) (hb : d375687 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375599, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107114 q ha hb
    | true =>
      simp only [d375599, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375600 q = 1) (hb : d375688 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375600, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375600, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375601 q = 1) (hb : d375689 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375601, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375601, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375602 q = 1) (hb : d375690 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375602, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375602, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375603 q = 1) (hb : d375691 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375603, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375603, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375604 q = 1) (hb : d375692 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375604, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375604, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107116 (p : Pattern) (ha : d375610 p = 1) (hb : d375698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375605 q = 1) (hb : d375693 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375605, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107115 q ha hb
    | true =>
      simp only [d375605, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375606 q = 1) (hb : d375694 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375606, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375606, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375607 q = 1) (hb : d375695 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375607, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375607, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375608 q = 1) (hb : d375696 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375608, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375608, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375609 q = 1) (hb : d375697 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375609, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375609, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375610 q = 1) (hb : d375698 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375610, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375610, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107117 (p : Pattern) (ha : d375616 p = 1) (hb : d375704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375611 q = 1) (hb : d375699 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375611, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107116 q ha hb
    | true =>
      simp only [d375611, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375612 q = 1) (hb : d375700 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375612, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375612, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375613 q = 1) (hb : d375701 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375613, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375613, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375614 q = 1) (hb : d375702 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375614, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375614, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375615 q = 1) (hb : d375703 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375615, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375615, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375616 q = 1) (hb : d375704 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375616, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375616, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107118 (p : Pattern) (ha : d375622 p = 1) (hb : d375710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375617 q = 1) (hb : d375705 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375617, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107117 q ha hb
    | true =>
      simp only [d375617, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375618 q = 1) (hb : d375706 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375618, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375618, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375619 q = 1) (hb : d375707 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375619, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375619, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375620 q = 1) (hb : d375708 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375620, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375620, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375621 q = 1) (hb : d375709 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375621, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375621, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375622 q = 1) (hb : d375710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375622, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375622, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107119 (p : Pattern) (ha : d375628 p = 1) (hb : d375716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375623 q = 1) (hb : d375711 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375623, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107118 q ha hb
    | true =>
      simp only [d375623, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375624 q = 1) (hb : d375712 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375624, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375624, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375625 q = 1) (hb : d375713 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375625, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375625, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375626 q = 1) (hb : d375714 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375626, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375626, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375627 q = 1) (hb : d375715 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375627, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375627, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375628 q = 1) (hb : d375716 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375628, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375628, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107120 (p : Pattern) (ha : d375634 p = 1) (hb : d375722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375629 q = 1) (hb : d375717 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375629, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107119 q ha hb
    | true =>
      simp only [d375629, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375630 q = 1) (hb : d375718 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375630, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375630, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375631 q = 1) (hb : d375719 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375631, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375631, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375632 q = 1) (hb : d375720 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375632, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375632, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375633 q = 1) (hb : d375721 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375633, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375633, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375634 q = 1) (hb : d375722 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375634, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375634, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107121 (p : Pattern) (ha : d375640 p = 1) (hb : d375728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375635 q = 1) (hb : d375723 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375635, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107120 q ha hb
    | true =>
      simp only [d375635, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d375636 q = 1) (hb : d375724 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375636, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375636, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d375637 q = 1) (hb : d375725 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375637, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375637, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d375638 q = 1) (hb : d375726 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375638, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375638, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d375639 q = 1) (hb : d375727 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375639, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375639, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d375640 q = 1) (hb : d375728 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375640, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375640, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107122 (p : Pattern) (ha : d375642 p = 1) (hb : d375686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d322122 q = 1) (hb : d367652 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105170 q ha hb
    | true =>
      simp only [d322122, d367652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105176 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322162 q = 1) (hb : d367679 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322162, d367679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105182 q ha hb
  have h3 (q : Pattern) (ha : d322163 q = 1) (hb : d367680 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d322163, d367680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322203 q = 1) (hb : d367707 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322203, d367707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105188 q ha hb
  have h5 (q : Pattern) (ha : d322204 q = 1) (hb : d367708 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322204, d367708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d322205 q = 1) (hb : d367709 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322205, d367709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d321678 q = 1) (hb : d321904 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321678, d321904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86389 q ha hb
  have h8 (q : Pattern) (ha : d321679 q = 1) (hb : d321905 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321679, d321905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d321680 q = 1) (hb : d321906 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321680, d321906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d322206 q = 1) (hb : d367710 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d322206, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d322206, d367710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d375641 q = 1) (hb : d375685 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d375641, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d375641, d375685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d375642 q = 1) (hb : d375686 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d375642, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d375642, d375686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h12 p ha hb
theorem andIntro107123 (p : Pattern) (ha : d375648 p = 1) (hb : d375692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375643 q = 1) (hb : d375687 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d375643, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107122 q ha hb
    | true =>
      simp only [d375643, d375687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375644 q = 1) (hb : d375688 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d375644, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375644, d375688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375645 q = 1) (hb : d375689 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d375645, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375645, d375689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375646 q = 1) (hb : d375690 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d375646, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375646, d375690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375647 q = 1) (hb : d375691 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d375647, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375647, d375691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375648 q = 1) (hb : d375692 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d375648, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375648, d375692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107124 (p : Pattern) (ha : d375654 p = 1) (hb : d375698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375649 q = 1) (hb : d375693 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d375649, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107123 q ha hb
    | true =>
      simp only [d375649, d375693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375650 q = 1) (hb : d375694 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d375650, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375650, d375694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375651 q = 1) (hb : d375695 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d375651, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375651, d375695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375652 q = 1) (hb : d375696 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d375652, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375652, d375696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375653 q = 1) (hb : d375697 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d375653, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375653, d375697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375654 q = 1) (hb : d375698 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d375654, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375654, d375698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107125 (p : Pattern) (ha : d375660 p = 1) (hb : d375704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375655 q = 1) (hb : d375699 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d375655, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107124 q ha hb
    | true =>
      simp only [d375655, d375699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375656 q = 1) (hb : d375700 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d375656, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375656, d375700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375657 q = 1) (hb : d375701 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d375657, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375657, d375701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375658 q = 1) (hb : d375702 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d375658, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375658, d375702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375659 q = 1) (hb : d375703 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d375659, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375659, d375703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375660 q = 1) (hb : d375704 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d375660, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375660, d375704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107126 (p : Pattern) (ha : d375666 p = 1) (hb : d375710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375661 q = 1) (hb : d375705 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d375661, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107125 q ha hb
    | true =>
      simp only [d375661, d375705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375662 q = 1) (hb : d375706 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d375662, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375662, d375706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375663 q = 1) (hb : d375707 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d375663, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375663, d375707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375664 q = 1) (hb : d375708 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d375664, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375664, d375708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375665 q = 1) (hb : d375709 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d375665, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375665, d375709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375666 q = 1) (hb : d375710 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d375666, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375666, d375710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107127 (p : Pattern) (ha : d375672 p = 1) (hb : d375716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375667 q = 1) (hb : d375711 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d375667, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107126 q ha hb
    | true =>
      simp only [d375667, d375711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375668 q = 1) (hb : d375712 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d375668, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375668, d375712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375669 q = 1) (hb : d375713 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d375669, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375669, d375713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375670 q = 1) (hb : d375714 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d375670, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375670, d375714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375671 q = 1) (hb : d375715 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d375671, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375671, d375715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375672 q = 1) (hb : d375716 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d375672, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375672, d375716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107128 (p : Pattern) (ha : d375678 p = 1) (hb : d375722 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375673 q = 1) (hb : d375717 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d375673, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107127 q ha hb
    | true =>
      simp only [d375673, d375717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375674 q = 1) (hb : d375718 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d375674, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375674, d375718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375675 q = 1) (hb : d375719 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d375675, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375675, d375719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375676 q = 1) (hb : d375720 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d375676, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375676, d375720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375677 q = 1) (hb : d375721 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d375677, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375677, d375721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375678 q = 1) (hb : d375722 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d375678, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375678, d375722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107129 (p : Pattern) (ha : d375684 p = 1) (hb : d375728 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d375679 q = 1) (hb : d375723 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d375679, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107128 q ha hb
    | true =>
      simp only [d375679, d375723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d375680 q = 1) (hb : d375724 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d375680, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d375680, d375724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d375681 q = 1) (hb : d375725 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d375681, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d375681, d375725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d375682 q = 1) (hb : d375726 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d375682, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d375682, d375726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d375683 q = 1) (hb : d375727 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d375683, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d375683, d375727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d375684 q = 1) (hb : d375728 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d375684, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d375684, d375728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107130 (p : Pattern) (ha : d322220 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322217 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d375732 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322218 q = 1) (hb : d375733 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d322218, d375733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322218, d375733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322219 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d375734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322219, d375734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d322220 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107131 (p : Pattern) (ha : d322226 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107130 q ha hb
    | true =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107132 (p : Pattern) (ha : d322232 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107131 q ha hb
    | true =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107133 (p : Pattern) (ha : d322238 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107132 q ha hb
    | true =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107134 (p : Pattern) (ha : d322244 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107133 q ha hb
    | true =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107135 (p : Pattern) (ha : d322250 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107134 q ha hb
    | true =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107136 (p : Pattern) (ha : d0 p = 1) (hb : d375820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375820 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107137 (p : Pattern) (ha : d367724 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d367721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d375732 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d367722 q = 1) (hb : d375733 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d375733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367722, d375733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d367723 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d375734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367723, d375734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d367724 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107138 (p : Pattern) (ha : d367730 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367725 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107137 q ha hb
    | true =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367726 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367727 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367728 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367729 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367730 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107139 (p : Pattern) (ha : d367736 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367731 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107138 q ha hb
    | true =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367732 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367733 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367734 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367735 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367736 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107140 (p : Pattern) (ha : d367742 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367737 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107139 q ha hb
    | true =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367738 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367739 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367740 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367741 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367742 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107141 (p : Pattern) (ha : d367748 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367743 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107140 q ha hb
    | true =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367744 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367745 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367746 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367747 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367748 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107142 (p : Pattern) (ha : d367754 p = 1) (hb : d375734 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367749 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107141 q ha hb
    | true =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367750 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367751 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367752 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367753 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367754 q = 1) (hb : d375734 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107143 (p : Pattern) (ha : d0 p = 1) (hb : d375863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375863 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro107144 (p : Pattern) (ha : d322220 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d322217 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d375864 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d322218 q = 1) (hb : d375865 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d322218, d375865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d322218, d375865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d322219 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d322219, d375866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322219, d375866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d322220 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107145 (p : Pattern) (ha : d322226 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322221 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107144 q ha hb
    | true =>
      simp only [d322221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322222 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322223 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322224 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322225 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322226 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107146 (p : Pattern) (ha : d322232 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322227 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107145 q ha hb
    | true =>
      simp only [d322227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322228 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322229 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322230 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322231 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322232 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107147 (p : Pattern) (ha : d322238 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322233 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107146 q ha hb
    | true =>
      simp only [d322233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322234 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322235 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322236 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322237 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322238 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107148 (p : Pattern) (ha : d322244 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322239 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107147 q ha hb
    | true =>
      simp only [d322239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322240 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322241 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322242 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322243 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322244 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107149 (p : Pattern) (ha : d322250 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d322245 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107148 q ha hb
    | true =>
      simp only [d322245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d322246 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d322246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d322247 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d322247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d322248 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d322249 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d322249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d322250 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d322250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107150 (p : Pattern) (ha : d367724 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d367721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d375864 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d367722 q = 1) (hb : d375865 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d367722, d375865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d367722, d375865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d367723 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d367723, d375866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367723, d375866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d367724 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107151 (p : Pattern) (ha : d367730 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367725 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107150 q ha hb
    | true =>
      simp only [d367725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367726 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367727 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367728 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367729 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367730 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107152 (p : Pattern) (ha : d367736 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367731 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107151 q ha hb
    | true =>
      simp only [d367731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367732 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367733 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367734 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367735 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367736 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107153 (p : Pattern) (ha : d367742 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367737 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107152 q ha hb
    | true =>
      simp only [d367737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367738 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367739 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367740 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367741 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367742 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107154 (p : Pattern) (ha : d367748 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367743 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107153 q ha hb
    | true =>
      simp only [d367743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367744 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367745 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367746 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367747 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367748 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107155 (p : Pattern) (ha : d367754 p = 1) (hb : d375866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d367749 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107154 q ha hb
    | true =>
      simp only [d367749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d367750 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d367750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d367751 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d367751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d367752 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d367752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d367753 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d367753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d367754 q = 1) (hb : d375866 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d367754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro107156 (p : Pattern) (ha : d308 p = 1) (hb : d46460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d1084 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d44996 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d44996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46459 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46460 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107157 (p : Pattern) (ha : d308 p = 1) (hb : d46466 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46461 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107156 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46462 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46463 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46464 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46465 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46466 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro107158 (p : Pattern) (ha : d308 p = 1) (hb : d46473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d13, d127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d14 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14, d308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d45587 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d45587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46472 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46473 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107159 (p : Pattern) (ha : d308 p = 1) (hb : d46482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46461 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107156 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46462 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46463 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46464 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46465 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46474 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107158 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46475 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46476 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46477 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107158 q ha hb
    | true =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46478 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d46479 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d46480 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d46481 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d46482 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro107160 (p : Pattern) (ha : d308 p = 1) (hb : d46488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46485 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46486 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46487 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46488 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107161 (p : Pattern) (ha : d308 p = 1) (hb : d46490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46485 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46486 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46487 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46489 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46490 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107162 (p : Pattern) (ha : d308 p = 1) (hb : d46494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46474 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107158 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d1115 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d1115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46475 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46476 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46477 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107158 q ha hb
    | true =>
      simp only [d46477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d19 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100106 q ha hb
    | true =>
      simp only [d19, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46478 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46479 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46480 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46481 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46494 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h11 p ha hb
theorem andIntro107163 (p : Pattern) (ha : d308 p = 1) (hb : d46500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46485 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46486 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46489 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46495 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107162 q ha hb
    | true =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46496 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46497 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46498 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46499 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46500 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107164 (p : Pattern) (ha : d308 p = 1) (hb : d46507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107160 q ha hb
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107161 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107161 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107163 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46502 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46503 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46504 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46505 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46506 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46507 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro107165 (p : Pattern) (ha : d308 p = 1) (hb : d46511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107161 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107163 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46502 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46503 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46505 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46510 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46511 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107166 (p : Pattern) (ha : d308 p = 1) (hb : d46517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107167 (p : Pattern) (ha : d308 p = 1) (hb : d46521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107168 (p : Pattern) (ha : d308 p = 1) (hb : d46527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107166 q ha hb
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107167 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46526 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46527 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107169 (p : Pattern) (ha : d308 p = 1) (hb : d46530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46530 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107170 (p : Pattern) (ha : d308 p = 1) (hb : d46531 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46531 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107171 (p : Pattern) (ha : d308 p = 1) (hb : d46537 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107166 q ha hb
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107167 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46526 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46532 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107169 q ha hb
    | true =>
      simp only [d46532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107170 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46533 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46534 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46535 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46536 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46537 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107172 (p : Pattern) (ha : d308 p = 1) (hb : d46693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107166 q ha hb
    | true =>
      simp only [d46522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107167 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46524 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46525 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46526 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107167 q ha hb
    | true =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46693 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107173 (p : Pattern) (ha : d308 p = 1) (hb : d46699 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46688 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107167 q ha hb
    | true =>
      simp only [d46688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46689 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46690 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46691 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46692 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107170 q ha hb
    | true =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46699 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107174 (p : Pattern) (ha : d308 p = 1) (hb : d46708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107170 q ha hb
    | true =>
      simp only [d46694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46698 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46708 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107175 (p : Pattern) (ha : d308 p = 1) (hb : d46730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46714 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46715 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46716 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46717 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46720 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46721 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46722 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46723 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46724 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d46729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d46730 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107176 (p : Pattern) (ha : d308 p = 1) (hb : d46740 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46720 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46721 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46722 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46723 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46729 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46735 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107162 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46495 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107162 q ha hb
    | true =>
      simp only [d46495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46736 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46496 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46737 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46738 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d46739 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d46740 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107177 (p : Pattern) (ha : d308 p = 1) (hb : d46759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46741 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107175 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107176 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46742 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46743 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46758 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46759 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107178 (p : Pattern) (ha : d308 p = 1) (hb : d46841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46760 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107177 q ha hb
    | true =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46761 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46838 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46839 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46840 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46841 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107179 (p : Pattern) (ha : d308 p = 1) (hb : d46847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46842 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107178 q ha hb
    | true =>
      simp only [d46842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46843 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46844 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46846 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46847 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107180 (p : Pattern) (ha : d308 p = 1) (hb : d46542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107181 (p : Pattern) (ha : d308 p = 1) (hb : d46544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46544 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107182 (p : Pattern) (ha : d308 p = 1) (hb : d46551 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46549 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46550 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46551 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107183 (p : Pattern) (ha : d308 p = 1) (hb : d46554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46554 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107184 (p : Pattern) (ha : d308 p = 1) (hb : d46558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46471 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46558 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107185 (p : Pattern) (ha : d308 p = 1) (hb : d46564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46559 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107184 q ha hb
    | true =>
      simp only [d46559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107160 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46560 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46561 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107160 q ha hb
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107161 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46562 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107161 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107163 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46502 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46503 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46504 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46563 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46564 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro107186 (p : Pattern) (ha : d308 p = 1) (hb : d46570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46565 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107185 q ha hb
    | true =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46566 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46567 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46568 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46569 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46570 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107187 (p : Pattern) (ha : d308 p = 1) (hb : d46637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46461 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107156 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d32155 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d32155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro100102 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46462 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46463 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46464 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46465 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46637 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro107188 (p : Pattern) (ha : d308 p = 1) (hb : d46643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46469 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46470 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46485 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46486 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46487 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46638 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107187 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46639 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46640 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46641 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d46642 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d46643 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107189 (p : Pattern) (ha : d308 p = 1) (hb : d46644 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46638 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107187 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46639 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46640 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46641 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46642 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46644 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107190 (p : Pattern) (ha : d308 p = 1) (hb : d46650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46491 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107160 q ha hb
    | true =>
      simp only [d46491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107161 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46492 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46493 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107161 q ha hb
    | true =>
      simp only [d46501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107163 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46502 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46503 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46504 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46645 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107188 q ha hb
    | true =>
      simp only [d46645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107189 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46646 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46647 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46648 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46649 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46650 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro107191 (p : Pattern) (ha : d308 p = 1) (hb : d46656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46651 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107190 q ha hb
    | true =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46652 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46653 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46654 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46655 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107192 (p : Pattern) (ha : d308 p = 1) (hb : d321643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107180 q ha hb
    | true =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107181 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107182 q ha hb
    | true =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107183 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107186 q ha hb
    | true =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107166 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d321639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107191 q ha hb
    | true =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d321640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d321641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d321642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d321643 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107193 (p : Pattern) (ha : d308 p = 1) (hb : d46663 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46663 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107194 (p : Pattern) (ha : d308 p = 1) (hb : d46664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46543 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46664 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107195 (p : Pattern) (ha : d308 p = 1) (hb : d46669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46549 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46550 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46669 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107196 (p : Pattern) (ha : d308 p = 1) (hb : d46670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107165 q ha hb
    | true =>
      simp only [d46512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46552 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46553 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107197 (p : Pattern) (ha : d308 p = 1) (hb : d46674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46565 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107185 q ha hb
    | true =>
      simp only [d46565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46566 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46508 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107164 q ha hb
    | true =>
      simp only [d46508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46509 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46567 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46568 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46569 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46674 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107198 (p : Pattern) (ha : d308 p = 1) (hb : d46680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46651 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107190 q ha hb
    | true =>
      simp only [d46651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46652 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46653 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46654 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46655 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107199 (p : Pattern) (ha : d308 p = 1) (hb : d321648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46545 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107180 q ha hb
    | true =>
      simp only [d46545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107181 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46546 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46547 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46548 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107182 q ha hb
    | true =>
      simp only [d46555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107183 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46556 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46557 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107186 q ha hb
    | true =>
      simp only [d46571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107166 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d321639 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46657 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107191 q ha hb
    | true =>
      simp only [d46657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46658 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d321640 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d321641 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d321642 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d46665 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107193 q ha hb
    | true =>
      simp only [d46665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107194 q ha hb
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d46666 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d46667 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d46668 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d46671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107195 q ha hb
    | true =>
      simp only [d46671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107196 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d46672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d46673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d46673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d46675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107197 q ha hb
    | true =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107169 q ha hb
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d321644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d308 q = 1) (hb : d46681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107198 q ha hb
    | true =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h25 (q : Pattern) (ha : d308 q = 1) (hb : d46682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d308 q = 1) (hb : d321645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d308 q = 1) (hb : d321646 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d321646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d308 q = 1) (hb : d321647 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d321647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d308 q = 1) (hb : d321648 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d321648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro107200 (p : Pattern) (ha : d308 p = 1) (hb : d321655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107197 q ha hb
    | true =>
      simp only [d46675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107169 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d321644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107198 q ha hb
    | true =>
      simp only [d46681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d321645 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d321653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d321654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d321655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107201 (p : Pattern) (ha : d308 p = 1) (hb : d46719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46714 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46715 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46716 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46717 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46718 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46719 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107202 (p : Pattern) (ha : d308 p = 1) (hb : d46725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46714 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46715 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46716 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46717 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46718 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46720 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46721 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46722 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46723 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d46724 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d46725 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107203 (p : Pattern) (ha : d308 p = 1) (hb : d46746 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46726 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107201 q ha hb
    | true =>
      simp only [d46726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107202 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46727 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46728 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46731 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107202 q ha hb
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107175 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46732 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46733 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46734 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46741 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107175 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107176 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46742 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46743 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46744 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46745 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46746 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro107204 (p : Pattern) (ha : d308 p = 1) (hb : d46751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46731 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107202 q ha hb
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107175 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46732 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46733 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46741 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107175 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107176 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46742 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46743 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46744 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46749 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46750 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46751 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro107205 (p : Pattern) (ha : d308 p = 1) (hb : d46757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46747 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107203 q ha hb
    | true =>
      simp only [d46747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46748 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107204 q ha hb
    | true =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46754 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46756 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46757 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107206 (p : Pattern) (ha : d308 p = 1) (hb : d46765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46752 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107204 q ha hb
    | true =>
      simp only [d46752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46753 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46760 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107177 q ha hb
    | true =>
      simp only [d46760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46761 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46762 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46763 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46764 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46765 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107207 (p : Pattern) (ha : d308 p = 1) (hb : d46817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46714 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46467 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107157 q ha hb
    | true =>
      simp only [d46467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46715 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46468 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46716 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46717 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46720 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46483 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107159 q ha hb
    | true =>
      simp only [d46483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46721 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46722 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46723 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d46723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46724 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d46812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107187 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d46638 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107187 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d46813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d46639 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d46814 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d46815 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d46816 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d46817 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d46817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro107208 (p : Pattern) (ha : d308 p = 1) (hb : d46818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46812 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107187 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46638 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107187 q ha hb
    | true =>
      simp only [d46638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46813 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46639 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46814 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46815 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46816 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46818 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107209 (p : Pattern) (ha : d308 p = 1) (hb : d46824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46731 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107202 q ha hb
    | true =>
      simp only [d46731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107175 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46732 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46733 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46741 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107175 q ha hb
    | true =>
      simp only [d46741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107176 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46742 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46743 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46744 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46819 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107207 q ha hb
    | true =>
      simp only [d46819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107208 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46820 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46821 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46822 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d46822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46823 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46824 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro107210 (p : Pattern) (ha : d308 p = 1) (hb : d46830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46825 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107209 q ha hb
    | true =>
      simp only [d46825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46826 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46827 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46828 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46829 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46830 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107211 (p : Pattern) (ha : d308 p = 1) (hb : d321665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46766 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107205 q ha hb
    | true =>
      simp only [d46766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107206 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d321661 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d321661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46831 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107210 q ha hb
    | true =>
      simp only [d46831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46832 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d321662 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d321662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d321663 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d321664 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d321665 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107212 (p : Pattern) (ha : d308 p = 1) (hb : d321671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46528 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107168 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46529 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46538 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107168 q ha hb
    | true =>
      simp only [d46538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107171 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46539 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46540 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d46540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d321649 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107192 q ha hb
    | true =>
      simp only [d321649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107199 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46700 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107172 q ha hb
    | true =>
      simp only [d46700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107173 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d321650 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d321650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d321651 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d321652 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d321652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d321656 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107200 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46709 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107174 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d321657 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d321657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d321658 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d321658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d321659 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d321659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d308 q = 1) (hb : d321660 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d321660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d308 q = 1) (hb : d321666 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d321666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107211 q ha hb
  have h18 (q : Pattern) (ha : d308 q = 1) (hb : d46848 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d46848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107179 q ha hb
  have h19 (q : Pattern) (ha : d308 q = 1) (hb : d321667 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d321667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d321667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d308 q = 1) (hb : d321668 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d321668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d321668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d308 q = 1) (hb : d321669 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d321669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d321669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d308 q = 1) (hb : d321670 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d321670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d321670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d308 q = 1) (hb : d321671 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d321671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d321671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro107213 (p : Pattern) (ha : d308 p = 1) (hb : d321677 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d321672 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d321672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107212 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d321673 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d321673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d321674 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d321674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d321675 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d321675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d321676 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d321676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d321677 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d321677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107214 (p : Pattern) (ha : d308 p = 1) (hb : d46867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d13 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d44880 q = 1) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d308, d44880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46864 q = 1) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46865 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46866 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46867 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h7 p ha hb
theorem andIntro107215 (p : Pattern) (ha : d308 p = 1) (hb : d46876 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46868 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107214 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46869 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107214 q ha hb
    | true =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46876 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro107216 (p : Pattern) (ha : d308 p = 1) (hb : d46882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46882 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107217 (p : Pattern) (ha : d308 p = 1) (hb : d46884 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46884 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro107218 (p : Pattern) (ha : d308 p = 1) (hb : d46888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46868 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107214 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46869 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46870 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107214 q ha hb
    | true =>
      simp only [d46871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46873 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46874 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46875 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46888 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d46888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h9 p ha hb
theorem andIntro107219 (p : Pattern) (ha : d308 p = 1) (hb : d46894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46883 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46889 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107218 q ha hb
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46890 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46891 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46892 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d46892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46893 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46894 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d46894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107220 (p : Pattern) (ha : d308 p = 1) (hb : d46901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107216 q ha hb
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107217 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107217 q ha hb
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107219 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46898 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46900 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46901 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro107221 (p : Pattern) (ha : d308 p = 1) (hb : d46905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107217 q ha hb
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107219 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46899 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46904 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46905 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107222 (p : Pattern) (ha : d308 p = 1) (hb : d46911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107220 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107223 (p : Pattern) (ha : d308 p = 1) (hb : d46915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107224 (p : Pattern) (ha : d308 p = 1) (hb : d46921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107222 q ha hb
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107223 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107225 (p : Pattern) (ha : d308 p = 1) (hb : d46924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107220 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107226 (p : Pattern) (ha : d308 p = 1) (hb : d46925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46925 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107227 (p : Pattern) (ha : d308 p = 1) (hb : d46931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107222 q ha hb
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107223 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107225 q ha hb
    | true =>
      simp only [d46926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107226 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46928 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46929 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46930 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46931 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d46931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107228 (p : Pattern) (ha : d308 p = 1) (hb : d47065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107222 q ha hb
    | true =>
      simp only [d46916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107223 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46919 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46920 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107223 q ha hb
    | true =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d47061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d47062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d47063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d47064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d47065 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107229 (p : Pattern) (ha : d308 p = 1) (hb : d47071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107223 q ha hb
    | true =>
      simp only [d47060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d47061 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47062 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d47063 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47064 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107226 q ha hb
    | true =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d47067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d47068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d47069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d47070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d47071 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro107230 (p : Pattern) (ha : d308 p = 1) (hb : d47080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47066 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107226 q ha hb
    | true =>
      simp only [d47066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d47067 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47068 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d47069 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47070 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47080 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107231 (p : Pattern) (ha : d308 p = 1) (hb : d47096 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d47090 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d47095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d47096 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro107232 (p : Pattern) (ha : d308 p = 1) (hb : d47106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47086 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47087 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d47087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47088 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47089 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d47095 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d47095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d47101 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107218 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46889 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107218 q ha hb
    | true =>
      simp only [d46889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d47102 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d47102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46890 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d46890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d47103 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d47103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d47104 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d47104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d47105 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d47105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d47105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d47106 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107233 (p : Pattern) (ha : d308 p = 1) (hb : d47125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47107 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107231 q ha hb
    | true =>
      simp only [d47107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107232 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d47108 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47109 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d47115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47124 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47125 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107234 (p : Pattern) (ha : d308 p = 1) (hb : d47216 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47126 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107233 q ha hb
    | true =>
      simp only [d47126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d47127 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47213 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d47214 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47215 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47216 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107235 (p : Pattern) (ha : d308 p = 1) (hb : d47222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47217 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107234 q ha hb
    | true =>
      simp only [d47217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d47218 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47219 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d47219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d47220 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d47220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47221 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d47222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107236 (p : Pattern) (ha : d308 p = 1) (hb : d46936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107220 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107237 (p : Pattern) (ha : d308 p = 1) (hb : d46938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46937 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46938 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107238 (p : Pattern) (ha : d308 p = 1) (hb : d46945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107220 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46943 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46944 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46945 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107239 (p : Pattern) (ha : d308 p = 1) (hb : d46948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46946 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46947 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46948 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107240 (p : Pattern) (ha : d308 p = 1) (hb : d46957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46952 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107216 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46953 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46954 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107216 q ha hb
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107217 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46955 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107217 q ha hb
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107219 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d46896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d46897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d46898 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d46956 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d46956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d46956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d46957 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d46957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d46957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro107241 (p : Pattern) (ha : d308 p = 1) (hb : d46963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46958 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107240 q ha hb
    | true =>
      simp only [d46958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46959 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107220 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46960 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46961 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46962 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46963 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d46963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro107242 (p : Pattern) (ha : d308 p = 1) (hb : d47016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46877 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107215 q ha hb
    | true =>
      simp only [d46877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46878 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d46878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46879 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46880 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46881 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47016 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d47016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107243 (p : Pattern) (ha : d308 p = 1) (hb : d47022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107216 q ha hb
    | true =>
      simp only [d46885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107217 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107217 q ha hb
    | true =>
      simp only [d46895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107219 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46898 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d47017 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d47017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107242 q ha hb
    | true =>
      simp only [d47017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d47018 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d47018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d47019 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d47019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d47020 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d47020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d47021 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d47021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d47022 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d47022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d47022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro107244 (p : Pattern) (ha : d308 p = 1) (hb : d47028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d47023 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d47023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107243 q ha hb
    | true =>
      simp only [d47023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d47024 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d47024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d47025 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d47025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d47025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d47026 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d47026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d47026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d47027 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d47027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d47027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47028 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d47028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro107245 (p : Pattern) (ha : d308 p = 1) (hb : d321686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107236 q ha hb
    | true =>
      simp only [d46939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107237 q ha hb
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46949 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107238 q ha hb
    | true =>
      simp only [d46949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107239 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46950 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d46950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46951 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d46951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d46964 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d46964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107241 q ha hb
    | true =>
      simp only [d46964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107222 q ha hb
  have h9 (q : Pattern) (ha : d308 q = 1) (hb : d321682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d321682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d308 q = 1) (hb : d47029 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d47029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107244 q ha hb
    | true =>
      simp only [d47029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d308 q = 1) (hb : d47030 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d47030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d47030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d308 q = 1) (hb : d321683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d321683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d308 q = 1) (hb : d321684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d321684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d308 q = 1) (hb : d321685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d321685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d308 q = 1) (hb : d321686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d321686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro107246 (p : Pattern) (ha : d308 p = 1) (hb : d47035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107220 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d46909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d47035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107247 (p : Pattern) (ha : d308 p = 1) (hb : d47036 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d46913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46937 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47036 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro107248 (p : Pattern) (ha : d308 p = 1) (hb : d47041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46902 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107220 q ha hb
    | true =>
      simp only [d46902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46903 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d46943 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d308 q = 1) (hb : d46944 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d46944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d308 q = 1) (hb : d47041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d47041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro107249 (p : Pattern) (ha : d308 p = 1) (hb : d47042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d308 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d308 q = 1) (hb : d46906 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107221 q ha hb
    | true =>
      simp only [d46906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d308 q = 1) (hb : d46907 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d308 q = 1) (hb : d46912 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d46912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d308 q = 1) (hb : d46946 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d46946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d308 q = 1) (hb : d46947 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d46947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d308 q = 1) (hb : d47042 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d47042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d47042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
end NetHack.Soko22Hazard87
