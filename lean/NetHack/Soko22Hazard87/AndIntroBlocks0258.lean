import NetHack.Soko22Hazard87.AndIntroBlocks0257
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro64500 (p : Pattern) (ha : d25532 p = 1) (hb : d208034 p = 1) : d240484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64473 q ha hb
    | true =>
      simp only [d25378, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25382 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64474 q ha hb
    | true =>
      simp only [d25382, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25383 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25384 q = 1) (hb : d208034 q = 1) : d240409 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25384, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25384, d240409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25419 q = 1) (hb : d208034 q = 1) : d240444 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25419, d240444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25419, d240444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25420 q = 1) (hb : d208034 q = 1) : d240445 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25420, d240445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25420, d240445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25532 q = 1) (hb : d208034 q = 1) : d240484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25532, d240484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25532, d240484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64501 (p : Pattern) (ha : d25533 p = 1) (hb : d208034 p = 1) : d240485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25382 q = 1) (hb : d208034 q = 1) : d240407 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25382, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64474 q ha hb
    | true =>
      simp only [d25382, d240407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25383 q = 1) (hb : d208034 q = 1) : d240408 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25383, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25383, d240408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25388 q = 1) (hb : d208034 q = 1) : d240413 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25388, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25388, d240413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25422 q = 1) (hb : d208034 q = 1) : d240447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25422, d240447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25422, d240447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25423 q = 1) (hb : d208034 q = 1) : d240448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25423, d240448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25423, d240448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25533 q = 1) (hb : d208034 q = 1) : d240485 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25533, d240485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25533, d240485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64502 (p : Pattern) (ha : d25537 p = 1) (hb : d208034 p = 1) : d240489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25468 q = 1) (hb : d208034 q = 1) : d240460 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25468, d240460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64494 q ha hb
    | true =>
      simp only [d25468, d240460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25469 q = 1) (hb : d208034 q = 1) : d240461 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25469, d240461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25469, d240461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25378 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64473 q ha hb
    | true =>
      simp only [d25378, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25379 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25470 q = 1) (hb : d208034 q = 1) : d240462 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25470, d240462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25470, d240462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25471 q = 1) (hb : d208034 q = 1) : d240463 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25471, d240463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25471, d240463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25472 q = 1) (hb : d208034 q = 1) : d240464 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25472, d240464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25472, d240464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25537 q = 1) (hb : d208034 q = 1) : d240489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25537, d240489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25537, d240489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64503 (p : Pattern) (ha : d25543 p = 1) (hb : d208034 p = 1) : d240492 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25378 q = 1) (hb : d208034 q = 1) : d240403 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25378, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64473 q ha hb
    | true =>
      simp only [d25378, d240403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25379 q = 1) (hb : d208034 q = 1) : d240404 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25379, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25379, d240404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25516 q = 1) (hb : d208034 q = 1) : d240468 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25516, d240468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25516, d240468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25517 q = 1) (hb : d208034 q = 1) : d240469 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25517, d240469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25517, d240469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25518 q = 1) (hb : d208034 q = 1) : d240470 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25518, d240470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25518, d240470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25543 q = 1) (hb : d208034 q = 1) : d240492 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25543, d240492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25543, d240492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64504 (p : Pattern) (ha : d202059 p = 1) (hb : d208034 p = 1) : d240498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25415 q = 1) (hb : d208034 q = 1) : d240440 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25415, d240440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64487 q ha hb
    | true =>
      simp only [d25415, d240440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64488 q ha hb
  have h2 (q : Pattern) (ha : d25416 q = 1) (hb : d208034 q = 1) : d240441 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25416, d240441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25416, d240441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25417 q = 1) (hb : d208034 q = 1) : d240442 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25417, d240442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25417, d240442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25418 q = 1) (hb : d208034 q = 1) : d240443 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25418, d240443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25418, d240443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25425 q = 1) (hb : d208034 q = 1) : d240450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25425, d240450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64489 q ha hb
    | true =>
      simp only [d25425, d240450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64490 q ha hb
  have h6 (q : Pattern) (ha : d25426 q = 1) (hb : d208034 q = 1) : d240451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25426, d240451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25426, d240451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25427 q = 1) (hb : d208034 q = 1) : d240452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25427, d240452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25427, d240452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25474 q = 1) (hb : d208034 q = 1) : d240466 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25474, d240466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64495 q ha hb
    | true =>
      simp only [d25474, d240466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64475 q ha hb
  have h9 (q : Pattern) (ha : d202050 q = 1) (hb : d208034 q = 1) : d240467 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202050, d240467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202050, d240467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25520 q = 1) (hb : d208034 q = 1) : d240472 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25520, d240472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64496 q ha hb
    | true =>
      simp only [d25520, d240472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25521 q = 1) (hb : d208034 q = 1) : d240473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25521, d240473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25521, d240473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202051 q = 1) (hb : d208034 q = 1) : d240474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202051, d240474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202051, d240474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202052 q = 1) (hb : d208034 q = 1) : d240475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202052, d240475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202052, d240475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202053 q = 1) (hb : d208034 q = 1) : d240476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202053, d240476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202053, d240476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25528 q = 1) (hb : d208034 q = 1) : d240480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25528, d240480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64498 q ha hb
    | true =>
      simp only [d25528, d240480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64499 q ha hb
  have h16 (q : Pattern) (ha : d25529 q = 1) (hb : d208034 q = 1) : d240481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25529, d240481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25529, d240481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25530 q = 1) (hb : d208034 q = 1) : d240482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25530, d240482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25530, d240482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25531 q = 1) (hb : d208034 q = 1) : d240483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25531, d240483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25531, d240483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25534 q = 1) (hb : d208034 q = 1) : d240486 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25534, d240486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64500 q ha hb
    | true =>
      simp only [d25534, d240486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64501 q ha hb
  have h20 (q : Pattern) (ha : d25535 q = 1) (hb : d208034 q = 1) : d240487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25535, d240487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25535, d240487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25536 q = 1) (hb : d208034 q = 1) : d240488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25536, d240488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25536, d240488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25538 q = 1) (hb : d208034 q = 1) : d240490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64502 q ha hb
    | true =>
      simp only [d25538, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64478 q ha hb
  have h23 (q : Pattern) (ha : d202055 q = 1) (hb : d208034 q = 1) : d240491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202055, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25544 q = 1) (hb : d208034 q = 1) : d240493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64503 q ha hb
    | true =>
      simp only [d25544, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25545 q = 1) (hb : d208034 q = 1) : d240494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25545, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202056 q = 1) (hb : d208034 q = 1) : d240495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202056, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202057 q = 1) (hb : d208034 q = 1) : d240496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202057, d240496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202057, d240496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202058 q = 1) (hb : d208034 q = 1) : d240497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202058, d240497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202058, d240497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202059 q = 1) (hb : d208034 q = 1) : d240498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202059, d240498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202059, d240498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro64505 (p : Pattern) (ha : d202066 p = 1) (hb : d208034 p = 1) : d240518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25538 q = 1) (hb : d208034 q = 1) : d240490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25538, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64502 q ha hb
    | true =>
      simp only [d25538, d240490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64478 q ha hb
  have h2 (q : Pattern) (ha : d202055 q = 1) (hb : d208034 q = 1) : d240491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202055, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202055, d240491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25544 q = 1) (hb : d208034 q = 1) : d240493 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25544, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64503 q ha hb
    | true =>
      simp only [d25544, d240493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25545 q = 1) (hb : d208034 q = 1) : d240494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25545, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25545, d240494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202056 q = 1) (hb : d208034 q = 1) : d240495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202056, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202056, d240495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202064 q = 1) (hb : d208034 q = 1) : d240516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202064, d240516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202064, d240516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202065 q = 1) (hb : d208034 q = 1) : d240517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202065, d240517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202065, d240517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202066 q = 1) (hb : d208034 q = 1) : d240518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202066, d240518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202066, d240518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64506 (p : Pattern) (ha : d25591 p = 1) (hb : d208034 p = 1) : d240526 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d208034 q = 1) : d25942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64491 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64491 q ha hb
    | true =>
      simp only [d25439, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d208034 q = 1) : d25943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d208034 q = 1) : d25944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d208034 q = 1) : d25945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64492 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64492 q ha hb
    | true =>
      simp only [d25444, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d208034 q = 1) : d25946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25590 q = 1) (hb : d208034 q = 1) : d25590 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25591 q = 1) (hb : d208034 q = 1) : d240526 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25591, d240526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25591, d240526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64507 (p : Pattern) (ha : d25601 p = 1) (hb : d208034 p = 1) : d240532 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25592 q = 1) (hb : d208034 q = 1) : d240527 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25592, d240527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64506 q ha hb
    | true =>
      simp only [d25592, d240527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64466 q ha hb
  have h2 (q : Pattern) (ha : d25593 q = 1) (hb : d208034 q = 1) : d240528 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25593, d240528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25593, d240528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25594 q = 1) (hb : d208034 q = 1) : d240529 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25594, d240529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25594, d240529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25595 q = 1) (hb : d208034 q = 1) : d25595 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25596 q = 1) (hb : d208034 q = 1) : d240364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25596, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64466 q ha hb
    | true =>
      simp only [d25596, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25597 q = 1) (hb : d208034 q = 1) : d240365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25597, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25597, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25598 q = 1) (hb : d208034 q = 1) : d240366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25598, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25598, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25599 q = 1) (hb : d208034 q = 1) : d240530 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25599, d240530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25599, d240530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25320 q = 1) (hb : d208034 q = 1) : d240364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64466 q ha hb
    | true =>
      simp only [d25320, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64444 q ha hb
  have h10 (q : Pattern) (ha : d25321 q = 1) (hb : d208034 q = 1) : d240365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25322 q = 1) (hb : d208034 q = 1) : d240366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d25154 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64444 q ha hb
    | true =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25155 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25156 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25323 q = 1) (hb : d208034 q = 1) : d240367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25323, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25600 q = 1) (hb : d208034 q = 1) : d240531 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25600, d240531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25600, d240531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25601 q = 1) (hb : d208034 q = 1) : d240532 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25601, d240532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d25601, d240532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro64508 (p : Pattern) (ha : d25606 p = 1) (hb : d208034 p = 1) : d240537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25320 q = 1) (hb : d208034 q = 1) : d240364 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25320, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64466 q ha hb
    | true =>
      simp only [d25320, d240364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64444 q ha hb
  have h2 (q : Pattern) (ha : d25321 q = 1) (hb : d208034 q = 1) : d240365 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25321, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25321, d240365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25322 q = 1) (hb : d208034 q = 1) : d240366 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25322, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25322, d240366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d208034 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d25154 q = 1) (hb : d208034 q = 1) : d240249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64444 q ha hb
    | true =>
      simp only [d25154, d240249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25155 q = 1) (hb : d208034 q = 1) : d240250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25155, d240250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25156 q = 1) (hb : d208034 q = 1) : d240251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25156, d240251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25323 q = 1) (hb : d208034 q = 1) : d240367 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25323, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25323, d240367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25604 q = 1) (hb : d208034 q = 1) : d240535 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25604, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25604, d240535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25605 q = 1) (hb : d208034 q = 1) : d240536 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25605, d240536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25605, d240536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25606 q = 1) (hb : d208034 q = 1) : d240537 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25606, d240537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25606, d240537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro64509 (p : Pattern) (ha : d25612 p = 1) (hb : d208034 p = 1) : d240543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25602 q = 1) (hb : d208034 q = 1) : d240533 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25602, d240533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64507 q ha hb
    | true =>
      simp only [d25602, d240533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25603 q = 1) (hb : d208034 q = 1) : d240534 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25603, d240534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25603, d240534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25607 q = 1) (hb : d208034 q = 1) : d240538 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64508 q ha hb
    | true =>
      simp only [d25607, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25608 q = 1) (hb : d208034 q = 1) : d240539 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25609 q = 1) (hb : d208034 q = 1) : d240540 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25609, d240540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25609, d240540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25610 q = 1) (hb : d208034 q = 1) : d240541 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25610, d240541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25610, d240541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25611 q = 1) (hb : d208034 q = 1) : d240542 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25611, d240542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25611, d240542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25612 q = 1) (hb : d208034 q = 1) : d240543 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25612, d240543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25612, d240543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64510 (p : Pattern) (ha : d25620 p = 1) (hb : d208034 p = 1) : d240551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d208034 q = 1) : d240538 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64508 q ha hb
    | true =>
      simp only [d25607, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d208034 q = 1) : d240539 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25615 q = 1) (hb : d208034 q = 1) : d240546 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25615, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64484 q ha hb
    | true =>
      simp only [d25615, d240546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25616 q = 1) (hb : d208034 q = 1) : d240547 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25616, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25616, d240547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25617 q = 1) (hb : d208034 q = 1) : d240548 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25617, d240548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25617, d240548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25618 q = 1) (hb : d208034 q = 1) : d240549 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25618, d240549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25618, d240549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25619 q = 1) (hb : d208034 q = 1) : d240550 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25619, d240550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25619, d240550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25620 q = 1) (hb : d208034 q = 1) : d240551 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25620, d240551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25620, d240551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64511 (p : Pattern) (ha : d25659 p = 1) (hb : d208034 p = 1) : d240557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25607 q = 1) (hb : d208034 q = 1) : d240538 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25607, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64508 q ha hb
    | true =>
      simp only [d25607, d240538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25608 q = 1) (hb : d208034 q = 1) : d240539 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25608, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25608, d240539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25656 q = 1) (hb : d208034 q = 1) : d240554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25656, d240554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25656, d240554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25657 q = 1) (hb : d208034 q = 1) : d240555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25657, d240555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25657, d240555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25658 q = 1) (hb : d208034 q = 1) : d240556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25658, d240556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25658, d240556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25659 q = 1) (hb : d208034 q = 1) : d240557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25659, d240557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25659, d240557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64512 (p : Pattern) (ha : d202076 p = 1) (hb : d208034 p = 1) : d240563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25621 q = 1) (hb : d208034 q = 1) : d240552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25621, d240552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64509 q ha hb
    | true =>
      simp only [d25621, d240552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64510 q ha hb
  have h2 (q : Pattern) (ha : d202072 q = 1) (hb : d208034 q = 1) : d240553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202072, d240553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202072, d240553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25660 q = 1) (hb : d208034 q = 1) : d240558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25660, d240558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64511 q ha hb
    | true =>
      simp only [d25660, d240558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25661 q = 1) (hb : d208034 q = 1) : d240559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25661, d240559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25661, d240559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202073 q = 1) (hb : d208034 q = 1) : d240560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202073, d240560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202073, d240560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202074 q = 1) (hb : d208034 q = 1) : d240561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202074, d240561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202074, d240561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202075 q = 1) (hb : d208034 q = 1) : d240562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202075, d240562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202075, d240562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202076 q = 1) (hb : d208034 q = 1) : d240563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202076, d240563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202076, d240563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64513 (p : Pattern) (ha : d202082 p = 1) (hb : d208034 p = 1) : d240580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25398 q = 1) (hb : d208034 q = 1) : d240423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25398, d240423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25398, d240423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64477 q ha hb
  have h2 (q : Pattern) (ha : d25399 q = 1) (hb : d208034 q = 1) : d240424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25399, d240424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25399, d240424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25408 q = 1) (hb : d208034 q = 1) : d240433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25408, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64477 q ha hb
    | true =>
      simp only [d25408, d240433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64480 q ha hb
  have h4 (q : Pattern) (ha : d25409 q = 1) (hb : d208034 q = 1) : d240434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25409, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25409, d240434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25410 q = 1) (hb : d208034 q = 1) : d240435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25410, d240435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25410, d240435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202060 q = 1) (hb : d208034 q = 1) : d240499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202060, d240499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64497 q ha hb
    | true =>
      simp only [d202060, d240499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64504 q ha hb
  have h7 (q : Pattern) (ha : d25563 q = 1) (hb : d208034 q = 1) : d240512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25563, d240512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64481 q ha hb
    | true =>
      simp only [d25563, d240512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64482 q ha hb
  have h8 (q : Pattern) (ha : d202061 q = 1) (hb : d208034 q = 1) : d240513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202061, d240513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202061, d240513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202062 q = 1) (hb : d208034 q = 1) : d240514 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202062, d240514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202062, d240514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202063 q = 1) (hb : d208034 q = 1) : d240515 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202063, d240515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202063, d240515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202067 q = 1) (hb : d208034 q = 1) : d240519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202067, d240519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202067, d240519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64505 q ha hb
  have h12 (q : Pattern) (ha : d25572 q = 1) (hb : d208034 q = 1) : d240521 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25572, d240521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25572, d240521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64483 q ha hb
  have h13 (q : Pattern) (ha : d202068 q = 1) (hb : d208034 q = 1) : d240522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202068, d240522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202068, d240522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202069 q = 1) (hb : d208034 q = 1) : d240523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202069, d240523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202069, d240523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202070 q = 1) (hb : d208034 q = 1) : d240524 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202070, d240524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202070, d240524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202071 q = 1) (hb : d208034 q = 1) : d240525 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202071, d240525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202071, d240525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202077 q = 1) (hb : d208034 q = 1) : d240564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202077, d240564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202077, d240564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64512 q ha hb
  have h18 (q : Pattern) (ha : d25677 q = 1) (hb : d208034 q = 1) : d240575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25677, d240575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25677, d240575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64486 q ha hb
  have h19 (q : Pattern) (ha : d202078 q = 1) (hb : d208034 q = 1) : d240576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202078, d240576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202078, d240576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202079 q = 1) (hb : d208034 q = 1) : d240577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202079, d240577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202079, d240577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202080 q = 1) (hb : d208034 q = 1) : d240578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202080, d240578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202080, d240578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202081 q = 1) (hb : d208034 q = 1) : d240579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202081, d240579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202081, d240579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202082 q = 1) (hb : d208034 q = 1) : d240580 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202082, d240580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202082, d240580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro64514 (p : Pattern) (ha : d202088 p = 1) (hb : d208034 p = 1) : d240586 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202083 q = 1) (hb : d208034 q = 1) : d240581 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202083, d240581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202083, d240581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64513 q ha hb
  have h2 (q : Pattern) (ha : d202084 q = 1) (hb : d208034 q = 1) : d240582 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202084, d240582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202084, d240582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202085 q = 1) (hb : d208034 q = 1) : d240583 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202085, d240583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202085, d240583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202086 q = 1) (hb : d208034 q = 1) : d240584 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202086, d240584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202086, d240584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202087 q = 1) (hb : d208034 q = 1) : d240585 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202087, d240585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202087, d240585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202088 q = 1) (hb : d208034 q = 1) : d240586 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202088, d240586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202088, d240586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64515 (p : Pattern) (ha : d25690 p = 1) (hb : d208034 p = 1) : d200353 p = 1 := by
  have h0 (q : Pattern) (ha : d9796 q = 1) (hb : d152852 q = 1) : d9796 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25102 q = 1) (hb : d208034 q = 1) : d25219 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25102, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25102, d208034, d25219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25103 q = 1) (hb : d208034 q = 1) : d25220 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25103, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25103, d25220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25690 q = 1) (hb : d208034 q = 1) : d200353 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25690, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25690, d200353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro64516 (p : Pattern) (ha : d25696 p = 1) (hb : d208034 p = 1) : d240589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25439 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64491 q ha hb
    | true =>
      simp only [d25439, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25440 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25440, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25441 q = 1) (hb : d208034 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25441, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25441, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25442 q = 1) (hb : d208034 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25442, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25442, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25444 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64492 q ha hb
    | true =>
      simp only [d25444, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25445 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25445, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25446 q = 1) (hb : d208034 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25446, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25446, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25447 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25447, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25447, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25448 q = 1) (hb : d208034 q = 1) : d25788 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25448, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25448, d25788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25455 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25693 q = 1) (hb : d208034 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25694 q = 1) (hb : d208034 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25695 q = 1) (hb : d208034 q = 1) : d240588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25695, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25695, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25696 q = 1) (hb : d208034 q = 1) : d240589 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25696, d240589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25696, d240589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro64517 (p : Pattern) (ha : d25699 p = 1) (hb : d208034 p = 1) : d240590 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25214 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64454 q ha hb
    | true =>
      simp only [d25214, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25215 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25215, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25216 q = 1) (hb : d208034 q = 1) : d25454 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25216, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25216, d25454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25217 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25217, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25217, d25455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25693 q = 1) (hb : d208034 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25694 q = 1) (hb : d208034 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25697 q = 1) (hb : d208034 q = 1) : d240588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25697, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25697, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25698 q = 1) (hb : d208034 q = 1) : d209918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25698, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25698, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25699 q = 1) (hb : d208034 q = 1) : d240590 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25699, d240590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25699, d240590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64518 (p : Pattern) (ha : d25703 p = 1) (hb : d208034 p = 1) : d209923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25693 q = 1) (hb : d208034 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25694 q = 1) (hb : d208034 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25698 q = 1) (hb : d208034 q = 1) : d209918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25698, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25698, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25703 q = 1) (hb : d208034 q = 1) : d209923 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25703, d209923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25703, d209923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64519 (p : Pattern) (ha : d25710 p = 1) (hb : d208034 p = 1) : d240600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25700 q = 1) (hb : d208034 q = 1) : d240591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64516 q ha hb
    | true =>
      simp only [d25700, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64517 q ha hb
  have h2 (q : Pattern) (ha : d25701 q = 1) (hb : d208034 q = 1) : d240592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25702 q = 1) (hb : d208034 q = 1) : d240593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25704 q = 1) (hb : d208034 q = 1) : d240594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64517 q ha hb
    | true =>
      simp only [d25704, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64518 q ha hb
  have h5 (q : Pattern) (ha : d25705 q = 1) (hb : d208034 q = 1) : d240595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25706 q = 1) (hb : d208034 q = 1) : d240596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25707 q = 1) (hb : d208034 q = 1) : d240597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25707, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25708 q = 1) (hb : d208034 q = 1) : d240598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25708, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25709 q = 1) (hb : d208034 q = 1) : d240599 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25709, d240599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25709, d240599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25710 q = 1) (hb : d208034 q = 1) : d240600 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25710, d240600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25710, d240600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64520 (p : Pattern) (ha : d25714 p = 1) (hb : d208034 p = 1) : d240604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25704 q = 1) (hb : d208034 q = 1) : d240594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64517 q ha hb
    | true =>
      simp only [d25704, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64518 q ha hb
  have h2 (q : Pattern) (ha : d25705 q = 1) (hb : d208034 q = 1) : d240595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25706 q = 1) (hb : d208034 q = 1) : d240596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25708 q = 1) (hb : d208034 q = 1) : d240598 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25708, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25708, d240598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25713 q = 1) (hb : d208034 q = 1) : d240603 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25713, d240603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25713, d240603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25714 q = 1) (hb : d208034 q = 1) : d240604 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25714, d240604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25714, d240604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64521 (p : Pattern) (ha : d25720 p = 1) (hb : d208034 p = 1) : d240610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d208034 q = 1) : d240609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25720 q = 1) (hb : d208034 q = 1) : d240610 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25720, d240610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25720, d240610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64522 (p : Pattern) (ha : d25724 p = 1) (hb : d208034 p = 1) : d240614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d208034 q = 1) : d240613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25724 q = 1) (hb : d208034 q = 1) : d240614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25724, d240614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25724, d240614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64523 (p : Pattern) (ha : d25730 p = 1) (hb : d208034 p = 1) : d240620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d208034 q = 1) : d240615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64521 q ha hb
    | true =>
      simp only [d25725, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64522 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d208034 q = 1) : d240616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d208034 q = 1) : d240617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d208034 q = 1) : d240618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d208034 q = 1) : d240619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25730 q = 1) (hb : d208034 q = 1) : d240620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25730, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25730, d240620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64524 (p : Pattern) (ha : d25733 p = 1) (hb : d208034 p = 1) : d240623 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25719 q = 1) (hb : d208034 q = 1) : d240609 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25719, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25719, d240609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25733 q = 1) (hb : d208034 q = 1) : d240623 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25733, d240623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25733, d240623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64525 (p : Pattern) (ha : d25734 p = 1) (hb : d208034 p = 1) : d240624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25723 q = 1) (hb : d208034 q = 1) : d240613 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25723, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25723, d240613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25734 q = 1) (hb : d208034 q = 1) : d240624 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25734, d240624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25734, d240624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64526 (p : Pattern) (ha : d25740 p = 1) (hb : d208034 p = 1) : d240630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d208034 q = 1) : d240615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64521 q ha hb
    | true =>
      simp only [d25725, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64522 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d208034 q = 1) : d240616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d208034 q = 1) : d240617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d208034 q = 1) : d240618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d208034 q = 1) : d240619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25735 q = 1) (hb : d208034 q = 1) : d240625 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25735, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64524 q ha hb
    | true =>
      simp only [d25735, d240625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64525 q ha hb
  have h7 (q : Pattern) (ha : d25736 q = 1) (hb : d208034 q = 1) : d240626 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25736, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25736, d240626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25737 q = 1) (hb : d208034 q = 1) : d240627 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25737, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25737, d240627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25738 q = 1) (hb : d208034 q = 1) : d240628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25738, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25738, d240628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25739 q = 1) (hb : d208034 q = 1) : d240629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25739, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25739, d240629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25740 q = 1) (hb : d208034 q = 1) : d240630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25740, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25740, d240630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64527 (p : Pattern) (ha : d25912 p = 1) (hb : d208034 p = 1) : d240709 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25725 q = 1) (hb : d208034 q = 1) : d240615 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25725, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64521 q ha hb
    | true =>
      simp only [d25725, d240615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64522 q ha hb
  have h2 (q : Pattern) (ha : d25726 q = 1) (hb : d208034 q = 1) : d240616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25726, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25726, d240616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25727 q = 1) (hb : d208034 q = 1) : d240617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25727, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25727, d240617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25728 q = 1) (hb : d208034 q = 1) : d240618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25728, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25728, d240618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25729 q = 1) (hb : d208034 q = 1) : d240619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25729, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25729, d240619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25907 q = 1) (hb : d208034 q = 1) : d240704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64522 q ha hb
    | true =>
      simp only [d25907, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25908 q = 1) (hb : d208034 q = 1) : d240705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25909 q = 1) (hb : d208034 q = 1) : d240706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25909, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25910 q = 1) (hb : d208034 q = 1) : d240707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25911 q = 1) (hb : d208034 q = 1) : d240708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25912 q = 1) (hb : d208034 q = 1) : d240709 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25912, d240709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25912, d240709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64528 (p : Pattern) (ha : d25918 p = 1) (hb : d208034 p = 1) : d240715 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25907 q = 1) (hb : d208034 q = 1) : d240704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25907, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64522 q ha hb
    | true =>
      simp only [d25907, d240704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25908 q = 1) (hb : d208034 q = 1) : d240705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25908, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25908, d240705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25909 q = 1) (hb : d208034 q = 1) : d240706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25909, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25909, d240706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25910 q = 1) (hb : d208034 q = 1) : d240707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25910, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25910, d240707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25911 q = 1) (hb : d208034 q = 1) : d240708 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25911, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25911, d240708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25913 q = 1) (hb : d208034 q = 1) : d240710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64525 q ha hb
    | true =>
      simp only [d25913, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25914 q = 1) (hb : d208034 q = 1) : d240711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25915 q = 1) (hb : d208034 q = 1) : d240712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25915, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25916 q = 1) (hb : d208034 q = 1) : d240713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25917 q = 1) (hb : d208034 q = 1) : d240714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25918 q = 1) (hb : d208034 q = 1) : d240715 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25918, d240715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25918, d240715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64529 (p : Pattern) (ha : d25927 p = 1) (hb : d208034 p = 1) : d240724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25913 q = 1) (hb : d208034 q = 1) : d240710 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25913, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64525 q ha hb
    | true =>
      simp only [d25913, d240710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25914 q = 1) (hb : d208034 q = 1) : d240711 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25914, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25914, d240711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25915 q = 1) (hb : d208034 q = 1) : d240712 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25915, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25915, d240712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25916 q = 1) (hb : d208034 q = 1) : d240713 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25916, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25916, d240713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25917 q = 1) (hb : d208034 q = 1) : d240714 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d25917, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25917, d240714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25927 q = 1) (hb : d208034 q = 1) : d240724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d25927, d240724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25927, d240724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64530 (p : Pattern) (ha : d25964 p = 1) (hb : d208034 p = 1) : d240741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25309 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25309, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25309, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64454 q ha hb
  have h2 (q : Pattern) (ha : d25214 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25214, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64454 q ha hb
    | true =>
      simp only [d25214, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25310 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25310, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25310, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25215 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25215, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25215, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25311 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25311, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25311, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25312 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25312, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25312, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25948 q = 1) (hb : d208034 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
  have h8 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25949 q = 1) (hb : d208034 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25950 q = 1) (hb : d208034 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25951 q = 1) (hb : d208034 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25963 q = 1) (hb : d208034 q = 1) : d240736 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25963, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25963, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25957 q = 1) (hb : d208034 q = 1) : d210060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25957, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d25957, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d25964 q = 1) (hb : d208034 q = 1) : d240741 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25964, d240741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25964, d240741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64531 (p : Pattern) (ha : d25968 p = 1) (hb : d208034 p = 1) : d210066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25948 q = 1) (hb : d208034 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
  have h2 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25949 q = 1) (hb : d208034 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25950 q = 1) (hb : d208034 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25951 q = 1) (hb : d208034 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25957 q = 1) (hb : d208034 q = 1) : d210060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25957, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25957, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25968 q = 1) (hb : d208034 q = 1) : d210066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25968, d210066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25968, d210066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64532 (p : Pattern) (ha : d25987 p = 1) (hb : d208034 p = 1) : d240764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25969 q = 1) (hb : d208034 q = 1) : d240746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64530 q ha hb
    | true =>
      simp only [d25969, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64531 q ha hb
  have h2 (q : Pattern) (ha : d25970 q = 1) (hb : d208034 q = 1) : d240747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25971 q = 1) (hb : d208034 q = 1) : d240748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25977 q = 1) (hb : d208034 q = 1) : d240754 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25977, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25977, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25986 q = 1) (hb : d208034 q = 1) : d240763 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25986, d240763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25986, d240763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25987 q = 1) (hb : d208034 q = 1) : d240764 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25987, d240764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25987, d240764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64533 (p : Pattern) (ha : d26058 p = 1) (hb : d208034 p = 1) : d240787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25988 q = 1) (hb : d208034 q = 1) : d240765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25988, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64532 q ha hb
    | true =>
      simp only [d25988, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25989 q = 1) (hb : d208034 q = 1) : d240766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25989, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25989, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26055 q = 1) (hb : d208034 q = 1) : d240784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26055, d240784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26055, d240784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26056 q = 1) (hb : d208034 q = 1) : d240785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26056, d240785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26056, d240785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26057 q = 1) (hb : d208034 q = 1) : d240786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26057, d240786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26057, d240786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26058 q = 1) (hb : d208034 q = 1) : d240787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26058, d240787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26058, d240787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64534 (p : Pattern) (ha : d26064 p = 1) (hb : d208034 p = 1) : d240793 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26059 q = 1) (hb : d208034 q = 1) : d240788 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26059, d240788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64533 q ha hb
    | true =>
      simp only [d26059, d240788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26060 q = 1) (hb : d208034 q = 1) : d240789 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26060, d240789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26060, d240789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26061 q = 1) (hb : d208034 q = 1) : d240790 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26061, d240790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26061, d240790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26062 q = 1) (hb : d208034 q = 1) : d240791 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26062, d240791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26062, d240791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26063 q = 1) (hb : d208034 q = 1) : d240792 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26063, d240792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26063, d240792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26064 q = 1) (hb : d208034 q = 1) : d240793 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26064, d240793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26064, d240793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64535 (p : Pattern) (ha : d25745 p = 1) (hb : d208034 p = 1) : d240635 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25744 q = 1) (hb : d208034 q = 1) : d240634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25744, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25744, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25745 q = 1) (hb : d208034 q = 1) : d240635 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25745, d240635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25745, d240635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64536 (p : Pattern) (ha : d25747 p = 1) (hb : d208034 p = 1) : d240637 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25746 q = 1) (hb : d208034 q = 1) : d240636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25746, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25746, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25747 q = 1) (hb : d208034 q = 1) : d240637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25747, d240637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25747, d240637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64537 (p : Pattern) (ha : d25754 p = 1) (hb : d208034 p = 1) : d240644 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25752 q = 1) (hb : d208034 q = 1) : d240642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25752, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25752, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25753 q = 1) (hb : d208034 q = 1) : d240643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25753, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25753, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25754 q = 1) (hb : d208034 q = 1) : d240644 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25754, d240644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25754, d240644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64538 (p : Pattern) (ha : d25757 p = 1) (hb : d208034 p = 1) : d240647 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25755 q = 1) (hb : d208034 q = 1) : d240645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25755, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25755, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25756 q = 1) (hb : d208034 q = 1) : d240646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25756, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25756, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25757 q = 1) (hb : d208034 q = 1) : d240647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25757, d240647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25757, d240647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64539 (p : Pattern) (ha : d25770 p = 1) (hb : d208034 p = 1) : d240651 p = 1 := by
  have h0 (q : Pattern) (ha : d9759 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25762 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25762, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25762, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25763 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25763, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25763, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25428 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25767 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d25768 q = 1) (hb : d208034 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25768, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25768, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d25769 q = 1) (hb : d208034 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25769, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25769, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d25770 q = 1) (hb : d208034 q = 1) : d240651 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25770, d240651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25770, d240651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64540 (p : Pattern) (ha : d25775 p = 1) (hb : d208034 p = 1) : d25783 p = 1 := by
  have h0 (q : Pattern) (ha : d25428 q = 1) (hb : d152852 q = 1) : d25428 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25430 q = 1) (hb : d208034 q = 1) : d25781 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25430, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25430, d208034, d25781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25431 q = 1) (hb : d208034 q = 1) : d25782 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25431, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25431, d25782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25450 q = 1) (hb : d208034 q = 1) : d25450 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d25775 q = 1) (hb : d208034 q = 1) : d25783 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d25775, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25775, d25783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64541 (p : Pattern) (ha : d25789 p = 1) (hb : d208034 p = 1) : d240657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25771 q = 1) (hb : d208034 q = 1) : d240652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25771, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64539 q ha hb
    | true =>
      simp only [d25771, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25772 q = 1) (hb : d208034 q = 1) : d240653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25772, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25772, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25773 q = 1) (hb : d208034 q = 1) : d240654 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25773, d240654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25773, d240654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25774 q = 1) (hb : d208034 q = 1) : d240655 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25774, d240655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25774, d240655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25776 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25776, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64540 q ha hb
    | true =>
      simp only [d25776, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25777 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25777, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25777, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25778 q = 1) (hb : d208034 q = 1) : d25786 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25778, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25778, d25786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25779 q = 1) (hb : d208034 q = 1) : d25787 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25779, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25779, d25787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25780 q = 1) (hb : d208034 q = 1) : d240656 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25780, d240656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25780, d240656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25788 q = 1) (hb : d208034 q = 1) : d25788 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d25789 q = 1) (hb : d208034 q = 1) : d240657 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25789, d240657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25789, d240657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64542 (p : Pattern) (ha : d25793 p = 1) (hb : d208034 p = 1) : d240590 p = 1 := by
  have h0 (q : Pattern) (ha : d25455 q = 1) (hb : d208034 q = 1) : d25455 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d25693 q = 1) (hb : d208034 q = 1) : d200356 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25693, d200356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25694 q = 1) (hb : d208034 q = 1) : d200357 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25694, d200357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d25695 q = 1) (hb : d208034 q = 1) : d240588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25695, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25695, d240588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25698 q = 1) (hb : d208034 q = 1) : d209918 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25698, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25698, d209918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d25793 q = 1) (hb : d208034 q = 1) : d240590 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25793, d240590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25793, d240590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64543 (p : Pattern) (ha : d25799 p = 1) (hb : d208034 p = 1) : d240663 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25790 q = 1) (hb : d208034 q = 1) : d240658 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25790, d240658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64541 q ha hb
    | true =>
      simp only [d25790, d240658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64516 q ha hb
  have h2 (q : Pattern) (ha : d25791 q = 1) (hb : d208034 q = 1) : d240659 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25791, d240659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25791, d240659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25792 q = 1) (hb : d208034 q = 1) : d240660 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25792, d240660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25792, d240660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25794 q = 1) (hb : d208034 q = 1) : d240591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25794, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64516 q ha hb
    | true =>
      simp only [d25794, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64542 q ha hb
  have h5 (q : Pattern) (ha : d25795 q = 1) (hb : d208034 q = 1) : d240592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25795, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25795, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25796 q = 1) (hb : d208034 q = 1) : d240593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25796, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25796, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25797 q = 1) (hb : d208034 q = 1) : d240661 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25797, d240661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25797, d240661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25700 q = 1) (hb : d208034 q = 1) : d240591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25700, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64516 q ha hb
    | true =>
      simp only [d25700, d240591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64517 q ha hb
  have h9 (q : Pattern) (ha : d25701 q = 1) (hb : d208034 q = 1) : d240592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25701, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25701, d240592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25702 q = 1) (hb : d208034 q = 1) : d240593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25702, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25702, d240593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25704 q = 1) (hb : d208034 q = 1) : d240594 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25704, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64517 q ha hb
    | true =>
      simp only [d25704, d240594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64518 q ha hb
  have h12 (q : Pattern) (ha : d25705 q = 1) (hb : d208034 q = 1) : d240595 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25705, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25705, d240595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25706 q = 1) (hb : d208034 q = 1) : d240596 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25706, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25706, d240596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25707 q = 1) (hb : d208034 q = 1) : d240597 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25707, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25707, d240597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25798 q = 1) (hb : d208034 q = 1) : d240662 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25798, d240662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25798, d240662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25799 q = 1) (hb : d208034 q = 1) : d240663 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25799, d240663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25799, d240663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro64544 (p : Pattern) (ha : d25805 p = 1) (hb : d208034 p = 1) : d240669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25800 q = 1) (hb : d208034 q = 1) : d240664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25800, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64543 q ha hb
    | true =>
      simp only [d25800, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25801 q = 1) (hb : d208034 q = 1) : d240665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25801, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25801, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25802 q = 1) (hb : d208034 q = 1) : d240666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25802, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25802, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25803 q = 1) (hb : d208034 q = 1) : d240667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25803, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25803, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25804 q = 1) (hb : d208034 q = 1) : d240668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25804, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25804, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25805 q = 1) (hb : d208034 q = 1) : d240669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25805, d240669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25805, d240669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64545 (p : Pattern) (ha : d25875 p = 1) (hb : d208034 p = 1) : d240675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25872 q = 1) (hb : d208034 q = 1) : d240672 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25872, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25872, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25873 q = 1) (hb : d208034 q = 1) : d240673 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25873, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25873, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25874 q = 1) (hb : d208034 q = 1) : d240674 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25874, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25874, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25875 q = 1) (hb : d208034 q = 1) : d240675 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25875, d240675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25875, d240675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64546 (p : Pattern) (ha : d202094 p = 1) (hb : d208034 p = 1) : d240681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25748 q = 1) (hb : d208034 q = 1) : d240638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25748, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64535 q ha hb
    | true =>
      simp only [d25748, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64536 q ha hb
  have h2 (q : Pattern) (ha : d25749 q = 1) (hb : d208034 q = 1) : d240639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25749, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25749, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25750 q = 1) (hb : d208034 q = 1) : d240640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25750, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25750, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25751 q = 1) (hb : d208034 q = 1) : d240641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25751, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25751, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25758 q = 1) (hb : d208034 q = 1) : d240648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25758, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64537 q ha hb
    | true =>
      simp only [d25758, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64538 q ha hb
  have h6 (q : Pattern) (ha : d25759 q = 1) (hb : d208034 q = 1) : d240649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25759, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25759, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25760 q = 1) (hb : d208034 q = 1) : d240650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25760, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25760, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25806 q = 1) (hb : d208034 q = 1) : d240670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25806, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64544 q ha hb
    | true =>
      simp only [d25806, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64521 q ha hb
  have h9 (q : Pattern) (ha : d202090 q = 1) (hb : d208034 q = 1) : d240671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202090, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25876 q = 1) (hb : d208034 q = 1) : d240676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25876, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64545 q ha hb
    | true =>
      simp only [d25876, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25877 q = 1) (hb : d208034 q = 1) : d240677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25877, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25877, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202091 q = 1) (hb : d208034 q = 1) : d240678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202091, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202092 q = 1) (hb : d208034 q = 1) : d240679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202092, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202093 q = 1) (hb : d208034 q = 1) : d240680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202093, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202094 q = 1) (hb : d208034 q = 1) : d240681 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202094, d240681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202094, d240681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64547 (p : Pattern) (ha : d25882 p = 1) (hb : d208034 p = 1) : d240682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25718 q = 1) (hb : d208034 q = 1) : d240608 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25718, d240608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25744 q = 1) (hb : d208034 q = 1) : d240634 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25744, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25744, d240634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25882 q = 1) (hb : d208034 q = 1) : d240682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25882, d240682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25882, d240682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64548 (p : Pattern) (ha : d25883 p = 1) (hb : d208034 p = 1) : d240683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25722 q = 1) (hb : d208034 q = 1) : d240612 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25722, d240612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25746 q = 1) (hb : d208034 q = 1) : d240636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25746, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25746, d240636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25883 q = 1) (hb : d208034 q = 1) : d240683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25883, d240683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25883, d240683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64549 (p : Pattern) (ha : d25888 p = 1) (hb : d208034 p = 1) : d240688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25717 q = 1) (hb : d208034 q = 1) : d240607 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25717, d240607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25752 q = 1) (hb : d208034 q = 1) : d240642 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25752, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25752, d240642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25753 q = 1) (hb : d208034 q = 1) : d240643 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25753, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25753, d240643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25888 q = 1) (hb : d208034 q = 1) : d240688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25888, d240688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25888, d240688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64550 (p : Pattern) (ha : d25889 p = 1) (hb : d208034 p = 1) : d240689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25715 q = 1) (hb : d208034 q = 1) : d240605 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64520 q ha hb
    | true =>
      simp only [d25715, d240605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25716 q = 1) (hb : d208034 q = 1) : d240606 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25716, d240606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25721 q = 1) (hb : d208034 q = 1) : d240611 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25721, d240611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25755 q = 1) (hb : d208034 q = 1) : d240645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25755, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25755, d240645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25756 q = 1) (hb : d208034 q = 1) : d240646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25756, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25756, d240646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25889 q = 1) (hb : d208034 q = 1) : d240689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25889, d240689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25889, d240689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64551 (p : Pattern) (ha : d25893 p = 1) (hb : d208034 p = 1) : d240693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25800 q = 1) (hb : d208034 q = 1) : d240664 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25800, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64543 q ha hb
    | true =>
      simp only [d25800, d240664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25801 q = 1) (hb : d208034 q = 1) : d240665 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25801, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25801, d240665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25802 q = 1) (hb : d208034 q = 1) : d240666 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25802, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25802, d240666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25803 q = 1) (hb : d208034 q = 1) : d240667 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25803, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25803, d240667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25804 q = 1) (hb : d208034 q = 1) : d240668 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25804, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25804, d240668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25893 q = 1) (hb : d208034 q = 1) : d240693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25893, d240693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25893, d240693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64552 (p : Pattern) (ha : d25899 p = 1) (hb : d208034 p = 1) : d240696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25711 q = 1) (hb : d208034 q = 1) : d240601 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64519 q ha hb
    | true =>
      simp only [d25711, d240601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25712 q = 1) (hb : d208034 q = 1) : d240602 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25712, d240602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25872 q = 1) (hb : d208034 q = 1) : d240672 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25872, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25872, d240672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25873 q = 1) (hb : d208034 q = 1) : d240673 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25873, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25873, d240673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25874 q = 1) (hb : d208034 q = 1) : d240674 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25874, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25874, d240674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d25899 q = 1) (hb : d208034 q = 1) : d240696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25899, d240696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25899, d240696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64553 (p : Pattern) (ha : d202099 p = 1) (hb : d208034 p = 1) : d240702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25748 q = 1) (hb : d208034 q = 1) : d240638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25748, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64535 q ha hb
    | true =>
      simp only [d25748, d240638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64536 q ha hb
  have h2 (q : Pattern) (ha : d25749 q = 1) (hb : d208034 q = 1) : d240639 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25749, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25749, d240639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25750 q = 1) (hb : d208034 q = 1) : d240640 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25750, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25750, d240640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25751 q = 1) (hb : d208034 q = 1) : d240641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25751, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25751, d240641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25758 q = 1) (hb : d208034 q = 1) : d240648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25758, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64537 q ha hb
    | true =>
      simp only [d25758, d240648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64538 q ha hb
  have h6 (q : Pattern) (ha : d25759 q = 1) (hb : d208034 q = 1) : d240649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25759, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25759, d240649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25760 q = 1) (hb : d208034 q = 1) : d240650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25760, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25760, d240650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25806 q = 1) (hb : d208034 q = 1) : d240670 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25806, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64544 q ha hb
    | true =>
      simp only [d25806, d240670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64521 q ha hb
  have h9 (q : Pattern) (ha : d202090 q = 1) (hb : d208034 q = 1) : d240671 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202090, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202090, d240671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d25876 q = 1) (hb : d208034 q = 1) : d240676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25876, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64545 q ha hb
    | true =>
      simp only [d25876, d240676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25877 q = 1) (hb : d208034 q = 1) : d240677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25877, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25877, d240677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202091 q = 1) (hb : d208034 q = 1) : d240678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202091, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202091, d240678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202092 q = 1) (hb : d208034 q = 1) : d240679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202092, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202092, d240679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202093 q = 1) (hb : d208034 q = 1) : d240680 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202093, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202093, d240680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25884 q = 1) (hb : d208034 q = 1) : d240684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25884, d240684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64547 q ha hb
    | true =>
      simp only [d25884, d240684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64548 q ha hb
  have h16 (q : Pattern) (ha : d25885 q = 1) (hb : d208034 q = 1) : d240685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25885, d240685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25885, d240685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d25886 q = 1) (hb : d208034 q = 1) : d240686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25886, d240686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25886, d240686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d25887 q = 1) (hb : d208034 q = 1) : d240687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d25887, d240687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25887, d240687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d25890 q = 1) (hb : d208034 q = 1) : d240690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25890, d240690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64549 q ha hb
    | true =>
      simp only [d25890, d240690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64550 q ha hb
  have h20 (q : Pattern) (ha : d25891 q = 1) (hb : d208034 q = 1) : d240691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25891, d240691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25891, d240691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d25892 q = 1) (hb : d208034 q = 1) : d240692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d25892, d240692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d25892, d240692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d25894 q = 1) (hb : d208034 q = 1) : d240694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25894, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64551 q ha hb
    | true =>
      simp only [d25894, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64524 q ha hb
  have h23 (q : Pattern) (ha : d202095 q = 1) (hb : d208034 q = 1) : d240695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202095, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d25900 q = 1) (hb : d208034 q = 1) : d240697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25900, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64552 q ha hb
    | true =>
      simp only [d25900, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d25901 q = 1) (hb : d208034 q = 1) : d240698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25901, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d25901, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202096 q = 1) (hb : d208034 q = 1) : d240699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202096, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202097 q = 1) (hb : d208034 q = 1) : d240700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202097, d240700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202097, d240700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202098 q = 1) (hb : d208034 q = 1) : d240701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202098, d240701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202098, d240701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202099 q = 1) (hb : d208034 q = 1) : d240702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202099, d240702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202099, d240702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro64554 (p : Pattern) (ha : d202106 p = 1) (hb : d208034 p = 1) : d240722 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25894 q = 1) (hb : d208034 q = 1) : d240694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25894, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64551 q ha hb
    | true =>
      simp only [d25894, d240694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64524 q ha hb
  have h2 (q : Pattern) (ha : d202095 q = 1) (hb : d208034 q = 1) : d240695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202095, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202095, d240695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25900 q = 1) (hb : d208034 q = 1) : d240697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25900, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64552 q ha hb
    | true =>
      simp only [d25900, d240697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25901 q = 1) (hb : d208034 q = 1) : d240698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d25901, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25901, d240698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202096 q = 1) (hb : d208034 q = 1) : d240699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202096, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202096, d240699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202104 q = 1) (hb : d208034 q = 1) : d240720 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202104, d240720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202104, d240720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202105 q = 1) (hb : d208034 q = 1) : d240721 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202105, d240721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202105, d240721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202106 q = 1) (hb : d208034 q = 1) : d240722 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202106, d240722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202106, d240722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64555 (p : Pattern) (ha : d25947 p = 1) (hb : d208034 p = 1) : d240735 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25933 q = 1) (hb : d208034 q = 1) : d240730 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25933, d240730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25933, d240730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64539 q ha hb
  have h2 (q : Pattern) (ha : d25771 q = 1) (hb : d208034 q = 1) : d240652 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25771, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64539 q ha hb
    | true =>
      simp only [d25771, d240652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25934 q = 1) (hb : d208034 q = 1) : d240731 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25934, d240731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25934, d240731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25772 q = 1) (hb : d208034 q = 1) : d240653 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25772, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25772, d240653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25935 q = 1) (hb : d208034 q = 1) : d240732 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25935, d240732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25935, d240732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25936 q = 1) (hb : d208034 q = 1) : d240733 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25936, d240733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25936, d240733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25937 q = 1) (hb : d208034 q = 1) : d25942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25937, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25937, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64540 q ha hb
  have h8 (q : Pattern) (ha : d25776 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25776, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64540 q ha hb
    | true =>
      simp only [d25776, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25938 q = 1) (hb : d208034 q = 1) : d25943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25938, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25938, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25777 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25777, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25777, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25939 q = 1) (hb : d208034 q = 1) : d25944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25939, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25939, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25940 q = 1) (hb : d208034 q = 1) : d25945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25940, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25940, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25941 q = 1) (hb : d208034 q = 1) : d240734 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25941, d240734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25941, d240734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25946 q = 1) (hb : d208034 q = 1) : d25946 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25947 q = 1) (hb : d208034 q = 1) : d240735 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25947, d240735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25947, d240735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64556 (p : Pattern) (ha : d25953 p = 1) (hb : d208034 p = 1) : d240737 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25577 q = 1) (hb : d208034 q = 1) : d25942 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25577, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25577, d25942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64491 q ha hb
  have h2 (q : Pattern) (ha : d25439 q = 1) (hb : d208034 q = 1) : d25784 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25439, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64491 q ha hb
    | true =>
      simp only [d25439, d25784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25578 q = 1) (hb : d208034 q = 1) : d25943 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25578, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25578, d25943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25440 q = 1) (hb : d208034 q = 1) : d25785 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25440, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25440, d25785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25579 q = 1) (hb : d208034 q = 1) : d25944 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25579, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25579, d25944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25580 q = 1) (hb : d208034 q = 1) : d25945 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25580, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25580, d25945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25581 q = 1) (hb : d208034 q = 1) : d25586 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25581, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25581, d25586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64492 q ha hb
  have h8 (q : Pattern) (ha : d25444 q = 1) (hb : d208034 q = 1) : d25452 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25444, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64492 q ha hb
    | true =>
      simp only [d25444, d25452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25582 q = 1) (hb : d208034 q = 1) : d25587 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25582, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25582, d25587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25445 q = 1) (hb : d208034 q = 1) : d25453 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25445, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25445, d25453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d25583 q = 1) (hb : d208034 q = 1) : d25588 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25583, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25583, d25588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d25584 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25584, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d25584, d25589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d25585 q = 1) (hb : d208034 q = 1) : d25946 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25585, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25585, d25946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25589 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d25948 q = 1) (hb : d208034 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
  have h16 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d25949 q = 1) (hb : d208034 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d25950 q = 1) (hb : d208034 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d25951 q = 1) (hb : d208034 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d25952 q = 1) (hb : d208034 q = 1) : d240736 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25952, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d25952, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d25953 q = 1) (hb : d208034 q = 1) : d240737 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25953, d240737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d25953, d240737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro64557 (p : Pattern) (ha : d25958 p = 1) (hb : d208034 p = 1) : d240741 p = 1 := by
  have h0 (q : Pattern) (ha : d25589 q = 1) (hb : d208034 q = 1) : d25589 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25948 q = 1) (hb : d208034 q = 1) : d200422 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25948, d200422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
  have h3 (q : Pattern) (ha : d25691 q = 1) (hb : d208034 q = 1) : d200354 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64515 q ha hb
    | true =>
      simp only [d25691, d200354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d25949 q = 1) (hb : d208034 q = 1) : d200423 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25949, d200423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25692 q = 1) (hb : d208034 q = 1) : d200355 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25692, d200355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d25950 q = 1) (hb : d208034 q = 1) : d200424 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d25950, d200424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25951 q = 1) (hb : d208034 q = 1) : d200425 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25951, d200425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d25952 q = 1) (hb : d208034 q = 1) : d240736 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25952, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25952, d240736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d25957 q = 1) (hb : d208034 q = 1) : d210060 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d25957, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25957, d210060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d25958 q = 1) (hb : d208034 q = 1) : d240741 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d25958, d240741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d25958, d240741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64558 (p : Pattern) (ha : d25974 p = 1) (hb : d208034 p = 1) : d240751 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25954 q = 1) (hb : d208034 q = 1) : d240738 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25954, d240738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64555 q ha hb
    | true =>
      simp only [d25954, d240738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64556 q ha hb
  have h2 (q : Pattern) (ha : d25955 q = 1) (hb : d208034 q = 1) : d240739 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25955, d240739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25955, d240739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25956 q = 1) (hb : d208034 q = 1) : d240740 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25956, d240740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25956, d240740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25959 q = 1) (hb : d208034 q = 1) : d240742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25959, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64556 q ha hb
    | true =>
      simp only [d25959, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64557 q ha hb
  have h5 (q : Pattern) (ha : d25960 q = 1) (hb : d208034 q = 1) : d240743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25960, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25960, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25961 q = 1) (hb : d208034 q = 1) : d240744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25961, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25961, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25962 q = 1) (hb : d208034 q = 1) : d240745 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25962, d240745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25962, d240745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25965 q = 1) (hb : d208034 q = 1) : d240742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25965, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64556 q ha hb
    | true =>
      simp only [d25965, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64530 q ha hb
  have h9 (q : Pattern) (ha : d25966 q = 1) (hb : d208034 q = 1) : d240743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25966, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25966, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25967 q = 1) (hb : d208034 q = 1) : d240744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25967, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25967, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25969 q = 1) (hb : d208034 q = 1) : d240746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64530 q ha hb
    | true =>
      simp only [d25969, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64531 q ha hb
  have h12 (q : Pattern) (ha : d25970 q = 1) (hb : d208034 q = 1) : d240747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d25971 q = 1) (hb : d208034 q = 1) : d240748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d25972 q = 1) (hb : d208034 q = 1) : d240749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25972, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25972, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d25973 q = 1) (hb : d208034 q = 1) : d240750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25973, d240750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25973, d240750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d25974 q = 1) (hb : d208034 q = 1) : d240751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25974, d240751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d25974, d240751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro64559 (p : Pattern) (ha : d25979 p = 1) (hb : d208034 p = 1) : d240756 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25965 q = 1) (hb : d208034 q = 1) : d240742 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25965, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64556 q ha hb
    | true =>
      simp only [d25965, d240742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64530 q ha hb
  have h2 (q : Pattern) (ha : d25966 q = 1) (hb : d208034 q = 1) : d240743 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25966, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25966, d240743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25967 q = 1) (hb : d208034 q = 1) : d240744 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25967, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25967, d240744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d25969 q = 1) (hb : d208034 q = 1) : d240746 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d25969, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64530 q ha hb
    | true =>
      simp only [d25969, d240746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64531 q ha hb
  have h5 (q : Pattern) (ha : d25970 q = 1) (hb : d208034 q = 1) : d240747 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d25970, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25970, d240747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25971 q = 1) (hb : d208034 q = 1) : d240748 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d25971, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25971, d240748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d25972 q = 1) (hb : d208034 q = 1) : d240749 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25972, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25972, d240749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d25977 q = 1) (hb : d208034 q = 1) : d240754 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d25977, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25977, d240754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d25978 q = 1) (hb : d208034 q = 1) : d240755 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d25978, d240755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25978, d240755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25979 q = 1) (hb : d208034 q = 1) : d240756 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d25979, d240756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d25979, d240756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64560 (p : Pattern) (ha : d25985 p = 1) (hb : d208034 p = 1) : d240762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25975 q = 1) (hb : d208034 q = 1) : d240752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25975, d240752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64558 q ha hb
    | true =>
      simp only [d25975, d240752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25976 q = 1) (hb : d208034 q = 1) : d240753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25976, d240753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25976, d240753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25980 q = 1) (hb : d208034 q = 1) : d240757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25980, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64559 q ha hb
    | true =>
      simp only [d25980, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25981 q = 1) (hb : d208034 q = 1) : d240758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25981, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25981, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25982 q = 1) (hb : d208034 q = 1) : d240759 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25982, d240759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25982, d240759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25983 q = 1) (hb : d208034 q = 1) : d240760 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25983, d240760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25983, d240760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25984 q = 1) (hb : d208034 q = 1) : d240761 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25984, d240761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25984, d240761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25985 q = 1) (hb : d208034 q = 1) : d240762 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25985, d240762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25985, d240762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64561 (p : Pattern) (ha : d25993 p = 1) (hb : d208034 p = 1) : d240770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25980 q = 1) (hb : d208034 q = 1) : d240757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25980, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64559 q ha hb
    | true =>
      simp only [d25980, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25981 q = 1) (hb : d208034 q = 1) : d240758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25981, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25981, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d25988 q = 1) (hb : d208034 q = 1) : d240765 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25988, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64532 q ha hb
    | true =>
      simp only [d25988, d240765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d25989 q = 1) (hb : d208034 q = 1) : d240766 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25989, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25989, d240766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d25990 q = 1) (hb : d208034 q = 1) : d240767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d25990, d240767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25990, d240767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d25991 q = 1) (hb : d208034 q = 1) : d240768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d25991, d240768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25991, d240768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d25992 q = 1) (hb : d208034 q = 1) : d240769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d25992, d240769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d25992, d240769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d25993 q = 1) (hb : d208034 q = 1) : d240770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d25993, d240770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25993, d240770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64562 (p : Pattern) (ha : d26047 p = 1) (hb : d208034 p = 1) : d240776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25980 q = 1) (hb : d208034 q = 1) : d240757 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d25980, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64559 q ha hb
    | true =>
      simp only [d25980, d240757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d25981 q = 1) (hb : d208034 q = 1) : d240758 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d25981, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25981, d240758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26044 q = 1) (hb : d208034 q = 1) : d240773 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26044, d240773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26044, d240773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26045 q = 1) (hb : d208034 q = 1) : d240774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26045, d240774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26045, d240774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26046 q = 1) (hb : d208034 q = 1) : d240775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26046, d240775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26046, d240775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26047 q = 1) (hb : d208034 q = 1) : d240776 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26047, d240776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26047, d240776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64563 (p : Pattern) (ha : d202116 p = 1) (hb : d208034 p = 1) : d240782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25994 q = 1) (hb : d208034 q = 1) : d240771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d25994, d240771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64560 q ha hb
    | true =>
      simp only [d25994, d240771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64561 q ha hb
  have h2 (q : Pattern) (ha : d202112 q = 1) (hb : d208034 q = 1) : d240772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202112, d240772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202112, d240772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26048 q = 1) (hb : d208034 q = 1) : d240777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26048, d240777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64562 q ha hb
    | true =>
      simp only [d26048, d240777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26049 q = 1) (hb : d208034 q = 1) : d240778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26049, d240778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26049, d240778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202113 q = 1) (hb : d208034 q = 1) : d240779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202113, d240779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202113, d240779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202114 q = 1) (hb : d208034 q = 1) : d240780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202114, d240780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202114, d240780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202115 q = 1) (hb : d208034 q = 1) : d240781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202115, d240781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202115, d240781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202116 q = 1) (hb : d208034 q = 1) : d240782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202116, d240782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202116, d240782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64564 (p : Pattern) (ha : d202122 p = 1) (hb : d208034 p = 1) : d240799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25731 q = 1) (hb : d208034 q = 1) : d240621 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25731, d240621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25731, d240621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64523 q ha hb
  have h2 (q : Pattern) (ha : d25732 q = 1) (hb : d208034 q = 1) : d240622 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25732, d240622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d25732, d240622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d25741 q = 1) (hb : d208034 q = 1) : d240631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25741, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64523 q ha hb
    | true =>
      simp only [d25741, d240631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64526 q ha hb
  have h4 (q : Pattern) (ha : d25742 q = 1) (hb : d208034 q = 1) : d240632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d25742, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d25742, d240632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d25743 q = 1) (hb : d208034 q = 1) : d240633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d25743, d240633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25743, d240633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202100 q = 1) (hb : d208034 q = 1) : d240703 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202100, d240703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64546 q ha hb
    | true =>
      simp only [d202100, d240703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64553 q ha hb
  have h7 (q : Pattern) (ha : d25919 q = 1) (hb : d208034 q = 1) : d240716 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25919, d240716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64527 q ha hb
    | true =>
      simp only [d25919, d240716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64528 q ha hb
  have h8 (q : Pattern) (ha : d202101 q = 1) (hb : d208034 q = 1) : d240717 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202101, d240717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202101, d240717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202102 q = 1) (hb : d208034 q = 1) : d240718 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202102, d240718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202102, d240718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202103 q = 1) (hb : d208034 q = 1) : d240719 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202103, d240719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202103, d240719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202107 q = 1) (hb : d208034 q = 1) : d240723 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202107, d240723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202107, d240723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64554 q ha hb
  have h12 (q : Pattern) (ha : d25928 q = 1) (hb : d208034 q = 1) : d240725 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d25928, d240725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25928, d240725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64529 q ha hb
  have h13 (q : Pattern) (ha : d202108 q = 1) (hb : d208034 q = 1) : d240726 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202108, d240726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202108, d240726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202109 q = 1) (hb : d208034 q = 1) : d240727 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202109, d240727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202109, d240727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202110 q = 1) (hb : d208034 q = 1) : d240728 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202110, d240728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202110, d240728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202111 q = 1) (hb : d208034 q = 1) : d240729 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202111, d240729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202111, d240729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202117 q = 1) (hb : d208034 q = 1) : d240783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202117, d240783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202117, d240783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64563 q ha hb
  have h18 (q : Pattern) (ha : d26065 q = 1) (hb : d208034 q = 1) : d240794 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26065, d240794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26065, d240794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64534 q ha hb
  have h19 (q : Pattern) (ha : d202118 q = 1) (hb : d208034 q = 1) : d240795 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202118, d240795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202118, d240795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202119 q = 1) (hb : d208034 q = 1) : d240796 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202119, d240796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202119, d240796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202120 q = 1) (hb : d208034 q = 1) : d240797 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202120, d240797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202120, d240797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202121 q = 1) (hb : d208034 q = 1) : d240798 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202121, d240798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202121, d240798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202122 q = 1) (hb : d208034 q = 1) : d240799 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202122, d240799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202122, d240799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro64565 (p : Pattern) (ha : d202128 p = 1) (hb : d208034 p = 1) : d240805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202123 q = 1) (hb : d208034 q = 1) : d240800 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202123, d240800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202123, d240800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64564 q ha hb
  have h2 (q : Pattern) (ha : d202124 q = 1) (hb : d208034 q = 1) : d240801 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202124, d240801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202124, d240801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202125 q = 1) (hb : d208034 q = 1) : d240802 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202125, d240802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202125, d240802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202126 q = 1) (hb : d208034 q = 1) : d240803 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202126, d240803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202126, d240803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202127 q = 1) (hb : d208034 q = 1) : d240804 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202127, d240804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202127, d240804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202128 q = 1) (hb : d208034 q = 1) : d240805 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202128, d240805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202128, d240805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64566 (p : Pattern) (ha : d26082 p = 1) (hb : d208034 p = 1) : d26199 p = 1 := by
  have h0 (q : Pattern) (ha : d9759 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25762 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25762, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25762, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25763 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25763, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25763, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26079 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25767 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26080 q = 1) (hb : d208034 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26080, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26080, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d26081 q = 1) (hb : d208034 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26081, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26081, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d26082 q = 1) (hb : d208034 q = 1) : d26199 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26082, d26199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26082, d26199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64567 (p : Pattern) (ha : d26092 p = 1) (hb : d208034 p = 1) : d26100 p = 1 := by
  have h0 (q : Pattern) (ha : d26079 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26087 q = 1) (hb : d208034 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26087, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26087, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26088 q = 1) (hb : d208034 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26088, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26088, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26091 q = 1) (hb : d208034 q = 1) : d26091 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26092 q = 1) (hb : d208034 q = 1) : d26100 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26092, d26100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26092, d26100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64568 (p : Pattern) (ha : d26107 p = 1) (hb : d208034 p = 1) : d240808 p = 1 := by
  have h0 (q : Pattern) (ha : d26089 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9796 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26105 q = 1) (hb : d208034 q = 1) : d26090 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26105, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26105, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26106 q = 1) (hb : d208034 q = 1) : d26091 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26106, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26106, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1132 q = 1) (hb : d152852 q = 1) : d1132 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d9841 q = 1) (hb : d208034 q = 1) : d1133 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9841, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d9842 q = 1) (hb : d208034 q = 1) : d1134 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9842, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d26107 q = 1) (hb : d208034 q = 1) : d240808 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26107, d240808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26107, d240808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64569 (p : Pattern) (ha : d26113 p = 1) (hb : d208034 p = 1) : d240814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26083 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26083, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64566 q ha hb
    | true =>
      simp only [d26083, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26084 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26084, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26084, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26085 q = 1) (hb : d208034 q = 1) : d26202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26085, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26085, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26086 q = 1) (hb : d208034 q = 1) : d26203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26086, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26086, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26093 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26093, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64567 q ha hb
    | true =>
      simp only [d26093, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26094 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26094, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26094, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26095 q = 1) (hb : d208034 q = 1) : d26103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26095, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26095, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26096 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26096, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26096, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26097 q = 1) (hb : d208034 q = 1) : d26204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26097, d26204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26097, d26204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26104 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26110 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26111 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26112 q = 1) (hb : d208034 q = 1) : d240813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26112, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26112, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26113 q = 1) (hb : d208034 q = 1) : d240814 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26113, d240814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26113, d240814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro64570 (p : Pattern) (ha : d26116 p = 1) (hb : d208034 p = 1) : d26100 p = 1 := by
  have h0 (q : Pattern) (ha : d26079 q = 1) (hb : d152852 q = 1) : d26079 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26087 q = 1) (hb : d208034 q = 1) : d26098 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26087, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26087, d208034, d26098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26088 q = 1) (hb : d208034 q = 1) : d26099 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26088, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26088, d26099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26089 q = 1) (hb : d152852 q = 1) : d26089 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25435 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26114 q = 1) (hb : d208034 q = 1) : d26090 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26114, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26114, d208034, d26090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d26115 q = 1) (hb : d208034 q = 1) : d26091 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26115, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26115, d26091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d26116 q = 1) (hb : d208034 q = 1) : d26100 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26116, d26100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26116, d26100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64571 (p : Pattern) (ha : d26123 p = 1) (hb : d208034 p = 1) : d240816 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26117 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26117, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64570 q ha hb
    | true =>
      simp only [d26117, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26118 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26118, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26118, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26119 q = 1) (hb : d208034 q = 1) : d26103 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26119, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26119, d26103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26120 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26120, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26120, d26104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26110 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26111 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26121 q = 1) (hb : d208034 q = 1) : d240813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26121, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26121, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26122 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26123 q = 1) (hb : d208034 q = 1) : d240816 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26123, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26123, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64572 (p : Pattern) (ha : d9843 p = 1) (hb : d208034 p = 1) : d1135 p = 1 := by
  have h0 (q : Pattern) (ha : d1132 q = 1) (hb : d152852 q = 1) : d1132 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9841 q = 1) (hb : d208034 q = 1) : d1133 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9841, d208034, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9842 q = 1) (hb : d208034 q = 1) : d1134 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9842, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9843 q = 1) (hb : d208034 q = 1) : d1135 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9843, d1135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9843, d1135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro64573 (p : Pattern) (ha : d26127 p = 1) (hb : d208034 p = 1) : d240820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26110 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26111 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26122 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d208034 q = 1) : d1136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64572 q ha hb
    | true =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d208034 q = 1) : d1137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d208034 q = 1) : d1138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d1138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d1138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d208034 q = 1) : d1139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d1139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d1139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d208034 q = 1) : d1140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d1140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d1140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26127 q = 1) (hb : d208034 q = 1) : d240820 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26127, d240820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26127, d240820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64574 (p : Pattern) (ha : d26134 p = 1) (hb : d208034 p = 1) : d240827 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26124 q = 1) (hb : d208034 q = 1) : d240817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26124, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64569 q ha hb
    | true =>
      simp only [d26124, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
  have h2 (q : Pattern) (ha : d26125 q = 1) (hb : d208034 q = 1) : d240818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26125, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26125, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26126 q = 1) (hb : d208034 q = 1) : d240819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26126, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26126, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26128 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
    | true =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64573 q ha hb
  have h5 (q : Pattern) (ha : d26129 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26130 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26131 q = 1) (hb : d208034 q = 1) : d240824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26131, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26131, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26132 q = 1) (hb : d208034 q = 1) : d240825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26132, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26132, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26133 q = 1) (hb : d208034 q = 1) : d240826 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26133, d240826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26133, d240826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26134 q = 1) (hb : d208034 q = 1) : d240827 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26134, d240827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26134, d240827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64575 (p : Pattern) (ha : d26138 p = 1) (hb : d208034 p = 1) : d240831 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26128 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
    | true =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64573 q ha hb
  have h2 (q : Pattern) (ha : d26129 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26130 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26132 q = 1) (hb : d208034 q = 1) : d240825 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26132, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26132, d240825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26137 q = 1) (hb : d208034 q = 1) : d240830 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26137, d240830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26137, d240830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26138 q = 1) (hb : d208034 q = 1) : d240831 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26138, d240831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26138, d240831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64576 (p : Pattern) (ha : d26144 p = 1) (hb : d208034 p = 1) : d240837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26143 q = 1) (hb : d208034 q = 1) : d240836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26143, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26143, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26144 q = 1) (hb : d208034 q = 1) : d240837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26144, d240837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26144, d240837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64577 (p : Pattern) (ha : d26148 p = 1) (hb : d208034 p = 1) : d240841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26147 q = 1) (hb : d208034 q = 1) : d240840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26147, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26147, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26148 q = 1) (hb : d208034 q = 1) : d240841 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26148, d240841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26148, d240841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64578 (p : Pattern) (ha : d26154 p = 1) (hb : d208034 p = 1) : d240847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26149 q = 1) (hb : d208034 q = 1) : d240842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26149, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64576 q ha hb
    | true =>
      simp only [d26149, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64577 q ha hb
  have h2 (q : Pattern) (ha : d26150 q = 1) (hb : d208034 q = 1) : d240843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26150, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26150, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26151 q = 1) (hb : d208034 q = 1) : d240844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26151, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26151, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26152 q = 1) (hb : d208034 q = 1) : d240845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26152, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26152, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26153 q = 1) (hb : d208034 q = 1) : d240846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26153, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26153, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26154 q = 1) (hb : d208034 q = 1) : d240847 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26154, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26154, d240847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64579 (p : Pattern) (ha : d26157 p = 1) (hb : d208034 p = 1) : d240850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26143 q = 1) (hb : d208034 q = 1) : d240836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26143, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26143, d240836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26157 q = 1) (hb : d208034 q = 1) : d240850 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26157, d240850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26157, d240850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64580 (p : Pattern) (ha : d26158 p = 1) (hb : d208034 p = 1) : d240851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26147 q = 1) (hb : d208034 q = 1) : d240840 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26147, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26147, d240840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26158 q = 1) (hb : d208034 q = 1) : d240851 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26158, d240851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26158, d240851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64581 (p : Pattern) (ha : d26164 p = 1) (hb : d208034 p = 1) : d240857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26149 q = 1) (hb : d208034 q = 1) : d240842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26149, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64576 q ha hb
    | true =>
      simp only [d26149, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64577 q ha hb
  have h2 (q : Pattern) (ha : d26150 q = 1) (hb : d208034 q = 1) : d240843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26150, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26150, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26151 q = 1) (hb : d208034 q = 1) : d240844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26151, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26151, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26152 q = 1) (hb : d208034 q = 1) : d240845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26152, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26152, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26153 q = 1) (hb : d208034 q = 1) : d240846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26153, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26153, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26159 q = 1) (hb : d208034 q = 1) : d240852 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26159, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64579 q ha hb
    | true =>
      simp only [d26159, d240852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64580 q ha hb
  have h7 (q : Pattern) (ha : d26160 q = 1) (hb : d208034 q = 1) : d240853 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26160, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26160, d240853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26161 q = 1) (hb : d208034 q = 1) : d240854 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26161, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26161, d240854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26162 q = 1) (hb : d208034 q = 1) : d240855 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26162, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26162, d240855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26163 q = 1) (hb : d208034 q = 1) : d240856 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26163, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26163, d240856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26164 q = 1) (hb : d208034 q = 1) : d240857 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26164, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26164, d240857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64582 (p : Pattern) (ha : d26352 p = 1) (hb : d208034 p = 1) : d240945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26149 q = 1) (hb : d208034 q = 1) : d240842 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26149, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64576 q ha hb
    | true =>
      simp only [d26149, d240842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64577 q ha hb
  have h2 (q : Pattern) (ha : d26150 q = 1) (hb : d208034 q = 1) : d240843 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26150, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26150, d240843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26151 q = 1) (hb : d208034 q = 1) : d240844 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26151, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26151, d240844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26152 q = 1) (hb : d208034 q = 1) : d240845 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26152, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26152, d240845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26153 q = 1) (hb : d208034 q = 1) : d240846 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26153, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26153, d240846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26347 q = 1) (hb : d208034 q = 1) : d240940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26347, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64577 q ha hb
    | true =>
      simp only [d26347, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26348 q = 1) (hb : d208034 q = 1) : d240941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26348, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26348, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26349 q = 1) (hb : d208034 q = 1) : d240942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26349, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26349, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26350 q = 1) (hb : d208034 q = 1) : d240943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26350, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26350, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26351 q = 1) (hb : d208034 q = 1) : d240944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26351, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26351, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26352 q = 1) (hb : d208034 q = 1) : d240945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26352, d240945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26352, d240945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64583 (p : Pattern) (ha : d26358 p = 1) (hb : d208034 p = 1) : d240951 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26347 q = 1) (hb : d208034 q = 1) : d240940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26347, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64577 q ha hb
    | true =>
      simp only [d26347, d240940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26348 q = 1) (hb : d208034 q = 1) : d240941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26348, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26348, d240941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26349 q = 1) (hb : d208034 q = 1) : d240942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26349, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26349, d240942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26350 q = 1) (hb : d208034 q = 1) : d240943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26350, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26350, d240943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26351 q = 1) (hb : d208034 q = 1) : d240944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26351, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26351, d240944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26353 q = 1) (hb : d208034 q = 1) : d240946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26353, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64580 q ha hb
    | true =>
      simp only [d26353, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26354 q = 1) (hb : d208034 q = 1) : d240947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26354, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26354, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26355 q = 1) (hb : d208034 q = 1) : d240948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26355, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26355, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26356 q = 1) (hb : d208034 q = 1) : d240949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26356, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26356, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26357 q = 1) (hb : d208034 q = 1) : d240950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26357, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26357, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26358 q = 1) (hb : d208034 q = 1) : d240951 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26358, d240951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26358, d240951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64584 (p : Pattern) (ha : d26367 p = 1) (hb : d208034 p = 1) : d240960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26353 q = 1) (hb : d208034 q = 1) : d240946 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26353, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64580 q ha hb
    | true =>
      simp only [d26353, d240946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26354 q = 1) (hb : d208034 q = 1) : d240947 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26354, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26354, d240947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26355 q = 1) (hb : d208034 q = 1) : d240948 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26355, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26355, d240948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26356 q = 1) (hb : d208034 q = 1) : d240949 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26356, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26356, d240949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26357 q = 1) (hb : d208034 q = 1) : d240950 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26357, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26357, d240950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26367 q = 1) (hb : d208034 q = 1) : d240960 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26367, d240960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26367, d240960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64585 (p : Pattern) (ha : d26421 p = 1) (hb : d208034 p = 1) : d240982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26416 q = 1) (hb : d208034 q = 1) : d26386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26416, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26416, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64570 q ha hb
  have h2 (q : Pattern) (ha : d26117 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26117, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64570 q ha hb
    | true =>
      simp only [d26117, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26417 q = 1) (hb : d208034 q = 1) : d26387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26417, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26417, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26118 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26118, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26118, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26418 q = 1) (hb : d208034 q = 1) : d26388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26418, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26418, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26419 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26419, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26419, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26401 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
  have h8 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26402 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26403 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26404 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26420 q = 1) (hb : d208034 q = 1) : d240976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26420, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26420, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26410 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26421 q = 1) (hb : d208034 q = 1) : d240982 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26421, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26421, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64586 (p : Pattern) (ha : d26425 p = 1) (hb : d208034 p = 1) : d240987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26401 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
  have h2 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26402 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26403 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26404 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26410 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d208034 q = 1) : d1406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d1406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d1406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64572 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d208034 q = 1) : d1136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64572 q ha hb
    | true =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d208034 q = 1) : d1407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d1407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d1407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d208034 q = 1) : d1137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d208034 q = 1) : d1408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d1408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d1408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d208034 q = 1) : d1409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d1409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d1409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d208034 q = 1) : d1410 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d1410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d1410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26425 q = 1) (hb : d208034 q = 1) : d240987 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26425, d240987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26425, d240987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64587 (p : Pattern) (ha : d26444 p = 1) (hb : d208034 p = 1) : d241006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26426 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
    | true =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64586 q ha hb
  have h2 (q : Pattern) (ha : d26427 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26428 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26434 q = 1) (hb : d208034 q = 1) : d240996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26434, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26434, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26443 q = 1) (hb : d208034 q = 1) : d241005 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26443, d241005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26443, d241005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26444 q = 1) (hb : d208034 q = 1) : d241006 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26444, d241006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26444, d241006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64588 (p : Pattern) (ha : d26528 p = 1) (hb : d208034 p = 1) : d241038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26445 q = 1) (hb : d208034 q = 1) : d241007 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26445, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64587 q ha hb
    | true =>
      simp only [d26445, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26446 q = 1) (hb : d208034 q = 1) : d241008 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26446, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26446, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26525 q = 1) (hb : d208034 q = 1) : d241035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26525, d241035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26525, d241035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26526 q = 1) (hb : d208034 q = 1) : d241036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26526, d241036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26526, d241036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26527 q = 1) (hb : d208034 q = 1) : d241037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26527, d241037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26527, d241037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26528 q = 1) (hb : d208034 q = 1) : d241038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26528, d241038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26528, d241038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64589 (p : Pattern) (ha : d26534 p = 1) (hb : d208034 p = 1) : d241044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26529 q = 1) (hb : d208034 q = 1) : d241039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26529, d241039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64588 q ha hb
    | true =>
      simp only [d26529, d241039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26530 q = 1) (hb : d208034 q = 1) : d241040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26530, d241040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26530, d241040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26531 q = 1) (hb : d208034 q = 1) : d241041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26531, d241041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26531, d241041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26532 q = 1) (hb : d208034 q = 1) : d241042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26532, d241042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26532, d241042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26533 q = 1) (hb : d208034 q = 1) : d241043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26533, d241043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26533, d241043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26534 q = 1) (hb : d208034 q = 1) : d241044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26534, d241044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26534, d241044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64590 (p : Pattern) (ha : d26169 p = 1) (hb : d208034 p = 1) : d240862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26168 q = 1) (hb : d208034 q = 1) : d240861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26168, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26168, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26169 q = 1) (hb : d208034 q = 1) : d240862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26169, d240862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26169, d240862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64591 (p : Pattern) (ha : d26171 p = 1) (hb : d208034 p = 1) : d240864 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26170 q = 1) (hb : d208034 q = 1) : d240863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26170, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26170, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26171 q = 1) (hb : d208034 q = 1) : d240864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26171, d240864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26171, d240864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64592 (p : Pattern) (ha : d26178 p = 1) (hb : d208034 p = 1) : d240871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26176 q = 1) (hb : d208034 q = 1) : d240869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26176, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26176, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26177 q = 1) (hb : d208034 q = 1) : d240870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26177, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26177, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26178 q = 1) (hb : d208034 q = 1) : d240871 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26178, d240871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26178, d240871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64593 (p : Pattern) (ha : d26181 p = 1) (hb : d208034 p = 1) : d240874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26179 q = 1) (hb : d208034 q = 1) : d240872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26179, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26179, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26180 q = 1) (hb : d208034 q = 1) : d240873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26180, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26180, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26181 q = 1) (hb : d208034 q = 1) : d240874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26181, d240874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26181, d240874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64594 (p : Pattern) (ha : d26188 p = 1) (hb : d208034 p = 1) : d240878 p = 1 := by
  have h0 (q : Pattern) (ha : d10042 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26185 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26186 q = 1) (hb : d208034 q = 1) : d10043 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26186, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26186, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26187 q = 1) (hb : d208034 q = 1) : d10044 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26187, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26187, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9761 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26188 q = 1) (hb : d208034 q = 1) : d240878 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26188, d240878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26188, d240878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64595 (p : Pattern) (ha : d26193 p = 1) (hb : d208034 p = 1) : d26199 p = 1 := by
  have h0 (q : Pattern) (ha : d9759 q = 1) (hb : d152852 q = 1) : d9759 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25761 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d25762 q = 1) (hb : d208034 q = 1) : d9760 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25762, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d25762, d208034, d9760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d25763 q = 1) (hb : d208034 q = 1) : d9761 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25763, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d25763, d9761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26099 q = 1) (hb : d208034 q = 1) : d26099 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26193 q = 1) (hb : d208034 q = 1) : d26199 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26193, d26199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26193, d26199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64596 (p : Pattern) (ha : d26205 p = 1) (hb : d208034 p = 1) : d240884 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26189 q = 1) (hb : d208034 q = 1) : d240879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26189, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64594 q ha hb
    | true =>
      simp only [d26189, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26190 q = 1) (hb : d208034 q = 1) : d240880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26190, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26190, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26191 q = 1) (hb : d208034 q = 1) : d240881 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26191, d240881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26191, d240881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26192 q = 1) (hb : d208034 q = 1) : d240882 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26192, d240882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26192, d240882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26194 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26194, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64595 q ha hb
    | true =>
      simp only [d26194, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26195 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26195, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26195, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26196 q = 1) (hb : d208034 q = 1) : d26202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26196, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26196, d26202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26197 q = 1) (hb : d208034 q = 1) : d26203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26197, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26197, d26203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26198 q = 1) (hb : d208034 q = 1) : d240883 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26198, d240883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26198, d240883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26204 q = 1) (hb : d208034 q = 1) : d26204 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26205 q = 1) (hb : d208034 q = 1) : d240884 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26205, d240884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26205, d240884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64597 (p : Pattern) (ha : d26209 p = 1) (hb : d208034 p = 1) : d240816 p = 1 := by
  have h0 (q : Pattern) (ha : d26104 q = 1) (hb : d208034 q = 1) : d26104 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26110 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26111 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26112 q = 1) (hb : d208034 q = 1) : d240813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26112, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26112, d240813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26122 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26209 q = 1) (hb : d208034 q = 1) : d240816 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26209, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26209, d240816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64598 (p : Pattern) (ha : d26215 p = 1) (hb : d208034 p = 1) : d240890 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26206 q = 1) (hb : d208034 q = 1) : d240885 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26206, d240885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64596 q ha hb
    | true =>
      simp only [d26206, d240885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64569 q ha hb
  have h2 (q : Pattern) (ha : d26207 q = 1) (hb : d208034 q = 1) : d240886 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26207, d240886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26207, d240886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26208 q = 1) (hb : d208034 q = 1) : d240887 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26208, d240887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26208, d240887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26210 q = 1) (hb : d208034 q = 1) : d240817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26210, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64569 q ha hb
    | true =>
      simp only [d26210, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64597 q ha hb
  have h5 (q : Pattern) (ha : d26211 q = 1) (hb : d208034 q = 1) : d240818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26211, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26211, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26212 q = 1) (hb : d208034 q = 1) : d240819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26212, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26212, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26213 q = 1) (hb : d208034 q = 1) : d240888 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26213, d240888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26213, d240888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26124 q = 1) (hb : d208034 q = 1) : d240817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26124, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64569 q ha hb
    | true =>
      simp only [d26124, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
  have h9 (q : Pattern) (ha : d26125 q = 1) (hb : d208034 q = 1) : d240818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26125, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26125, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26126 q = 1) (hb : d208034 q = 1) : d240819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26126, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26126, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26128 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
    | true =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64573 q ha hb
  have h12 (q : Pattern) (ha : d26129 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26130 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26131 q = 1) (hb : d208034 q = 1) : d240824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26131, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26131, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26214 q = 1) (hb : d208034 q = 1) : d240889 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26214, d240889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26214, d240889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26215 q = 1) (hb : d208034 q = 1) : d240890 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26215, d240890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26215, d240890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro64599 (p : Pattern) (ha : d26221 p = 1) (hb : d208034 p = 1) : d240896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26216 q = 1) (hb : d208034 q = 1) : d240891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26216, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64598 q ha hb
    | true =>
      simp only [d26216, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26217 q = 1) (hb : d208034 q = 1) : d240892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26217, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26217, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26218 q = 1) (hb : d208034 q = 1) : d240893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26218, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26218, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26219 q = 1) (hb : d208034 q = 1) : d240894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26219, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26219, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26220 q = 1) (hb : d208034 q = 1) : d240895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26220, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26220, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26221 q = 1) (hb : d208034 q = 1) : d240896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26221, d240896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26221, d240896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64600 (p : Pattern) (ha : d26303 p = 1) (hb : d208034 p = 1) : d240899 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26110 q = 1) (hb : d208034 q = 1) : d240811 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26110, d240811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26111 q = 1) (hb : d208034 q = 1) : d240812 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26111, d240812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26122 q = 1) (hb : d208034 q = 1) : d240815 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26122, d240815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26303 q = 1) (hb : d208034 q = 1) : d240899 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26303, d240899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26303, d240899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64601 (p : Pattern) (ha : d26309 p = 1) (hb : d208034 p = 1) : d240905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26124 q = 1) (hb : d208034 q = 1) : d240817 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26124, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64569 q ha hb
    | true =>
      simp only [d26124, d240817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
  have h2 (q : Pattern) (ha : d26125 q = 1) (hb : d208034 q = 1) : d240818 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26125, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26125, d240818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26126 q = 1) (hb : d208034 q = 1) : d240819 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26126, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26126, d240819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26128 q = 1) (hb : d208034 q = 1) : d240821 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
    | true =>
      simp only [d26128, d240821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64573 q ha hb
  have h5 (q : Pattern) (ha : d26129 q = 1) (hb : d208034 q = 1) : d240822 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26129, d240822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26130 q = 1) (hb : d208034 q = 1) : d240823 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26130, d240823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26131 q = 1) (hb : d208034 q = 1) : d240824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26131, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26131, d240824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26304 q = 1) (hb : d208034 q = 1) : d240900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26304, d240900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64571 q ha hb
    | true =>
      simp only [d26304, d240900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64600 q ha hb
  have h9 (q : Pattern) (ha : d26305 q = 1) (hb : d208034 q = 1) : d240901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26305, d240901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26305, d240901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26306 q = 1) (hb : d208034 q = 1) : d240902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26306, d240902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26306, d240902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26307 q = 1) (hb : d208034 q = 1) : d240903 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26307, d240903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26307, d240903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26308 q = 1) (hb : d208034 q = 1) : d240904 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26308, d240904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26308, d240904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26309 q = 1) (hb : d208034 q = 1) : d240905 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26309, d240905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26309, d240905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro64602 (p : Pattern) (ha : d26315 p = 1) (hb : d208034 p = 1) : d240911 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26310 q = 1) (hb : d208034 q = 1) : d240906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26310, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64601 q ha hb
    | true =>
      simp only [d26310, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26311 q = 1) (hb : d208034 q = 1) : d240907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26311, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26311, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26312 q = 1) (hb : d208034 q = 1) : d240908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26312, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26312, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26313 q = 1) (hb : d208034 q = 1) : d240909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26313, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26313, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26314 q = 1) (hb : d208034 q = 1) : d240910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26314, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26314, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26315 q = 1) (hb : d208034 q = 1) : d240911 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26315, d240911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26315, d240911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64603 (p : Pattern) (ha : d202135 p = 1) (hb : d208034 p = 1) : d240917 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26172 q = 1) (hb : d208034 q = 1) : d240865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26172, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64590 q ha hb
    | true =>
      simp only [d26172, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64591 q ha hb
  have h2 (q : Pattern) (ha : d26173 q = 1) (hb : d208034 q = 1) : d240866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26173, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26173, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26174 q = 1) (hb : d208034 q = 1) : d240867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26174, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26174, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26175 q = 1) (hb : d208034 q = 1) : d240868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26175, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26175, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26182 q = 1) (hb : d208034 q = 1) : d240875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26182, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64592 q ha hb
    | true =>
      simp only [d26182, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64593 q ha hb
  have h6 (q : Pattern) (ha : d26183 q = 1) (hb : d208034 q = 1) : d240876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26183, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26183, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26184 q = 1) (hb : d208034 q = 1) : d240877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26184, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26184, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26222 q = 1) (hb : d208034 q = 1) : d240897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26222, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64599 q ha hb
    | true =>
      simp only [d26222, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64576 q ha hb
  have h9 (q : Pattern) (ha : d202131 q = 1) (hb : d208034 q = 1) : d240898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202131, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d26316 q = 1) (hb : d208034 q = 1) : d240912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26316, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64602 q ha hb
    | true =>
      simp only [d26316, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26317 q = 1) (hb : d208034 q = 1) : d240913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26317, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26317, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202132 q = 1) (hb : d208034 q = 1) : d240914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202132, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202133 q = 1) (hb : d208034 q = 1) : d240915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202133, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202134 q = 1) (hb : d208034 q = 1) : d240916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202134, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202135 q = 1) (hb : d208034 q = 1) : d240917 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202135, d240917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202135, d240917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64604 (p : Pattern) (ha : d26322 p = 1) (hb : d208034 p = 1) : d240918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26142 q = 1) (hb : d208034 q = 1) : d240835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26142, d240835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26168 q = 1) (hb : d208034 q = 1) : d240861 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26168, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26168, d240861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26322 q = 1) (hb : d208034 q = 1) : d240918 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26322, d240918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26322, d240918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64605 (p : Pattern) (ha : d26323 p = 1) (hb : d208034 p = 1) : d240919 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26146 q = 1) (hb : d208034 q = 1) : d240839 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26146, d240839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26170 q = 1) (hb : d208034 q = 1) : d240863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26170, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26170, d240863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26323 q = 1) (hb : d208034 q = 1) : d240919 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26323, d240919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26323, d240919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64606 (p : Pattern) (ha : d26328 p = 1) (hb : d208034 p = 1) : d240924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26141 q = 1) (hb : d208034 q = 1) : d240834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26141, d240834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26176 q = 1) (hb : d208034 q = 1) : d240869 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26176, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26176, d240869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26177 q = 1) (hb : d208034 q = 1) : d240870 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26177, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26177, d240870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26328 q = 1) (hb : d208034 q = 1) : d240924 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26328, d240924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26328, d240924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64607 (p : Pattern) (ha : d26329 p = 1) (hb : d208034 p = 1) : d240925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26139 q = 1) (hb : d208034 q = 1) : d240832 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64575 q ha hb
    | true =>
      simp only [d26139, d240832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26140 q = 1) (hb : d208034 q = 1) : d240833 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26140, d240833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26145 q = 1) (hb : d208034 q = 1) : d240838 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26145, d240838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26179 q = 1) (hb : d208034 q = 1) : d240872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26179, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26179, d240872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26180 q = 1) (hb : d208034 q = 1) : d240873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26180, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26180, d240873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26329 q = 1) (hb : d208034 q = 1) : d240925 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26329, d240925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26329, d240925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64608 (p : Pattern) (ha : d26333 p = 1) (hb : d208034 p = 1) : d240929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26216 q = 1) (hb : d208034 q = 1) : d240891 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26216, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64598 q ha hb
    | true =>
      simp only [d26216, d240891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26217 q = 1) (hb : d208034 q = 1) : d240892 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26217, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26217, d240892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26135 q = 1) (hb : d208034 q = 1) : d240828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64574 q ha hb
    | true =>
      simp only [d26135, d240828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26136 q = 1) (hb : d208034 q = 1) : d240829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26136, d240829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26218 q = 1) (hb : d208034 q = 1) : d240893 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26218, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26218, d240893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26219 q = 1) (hb : d208034 q = 1) : d240894 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26219, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26219, d240894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26220 q = 1) (hb : d208034 q = 1) : d240895 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26220, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26220, d240895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26333 q = 1) (hb : d208034 q = 1) : d240929 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26333, d240929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26333, d240929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64609 (p : Pattern) (ha : d26339 p = 1) (hb : d208034 p = 1) : d240932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26310 q = 1) (hb : d208034 q = 1) : d240906 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26310, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64601 q ha hb
    | true =>
      simp only [d26310, d240906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26311 q = 1) (hb : d208034 q = 1) : d240907 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26311, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26311, d240907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26312 q = 1) (hb : d208034 q = 1) : d240908 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26312, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26312, d240908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26313 q = 1) (hb : d208034 q = 1) : d240909 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26313, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26313, d240909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26314 q = 1) (hb : d208034 q = 1) : d240910 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26314, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26314, d240910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26339 q = 1) (hb : d208034 q = 1) : d240932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26339, d240932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26339, d240932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64610 (p : Pattern) (ha : d202140 p = 1) (hb : d208034 p = 1) : d240938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26172 q = 1) (hb : d208034 q = 1) : d240865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26172, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64590 q ha hb
    | true =>
      simp only [d26172, d240865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64591 q ha hb
  have h2 (q : Pattern) (ha : d26173 q = 1) (hb : d208034 q = 1) : d240866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26173, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26173, d240866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26174 q = 1) (hb : d208034 q = 1) : d240867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26174, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26174, d240867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26175 q = 1) (hb : d208034 q = 1) : d240868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26175, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26175, d240868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26182 q = 1) (hb : d208034 q = 1) : d240875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26182, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64592 q ha hb
    | true =>
      simp only [d26182, d240875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64593 q ha hb
  have h6 (q : Pattern) (ha : d26183 q = 1) (hb : d208034 q = 1) : d240876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26183, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26183, d240876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26184 q = 1) (hb : d208034 q = 1) : d240877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26184, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26184, d240877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26222 q = 1) (hb : d208034 q = 1) : d240897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26222, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64599 q ha hb
    | true =>
      simp only [d26222, d240897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64576 q ha hb
  have h9 (q : Pattern) (ha : d202131 q = 1) (hb : d208034 q = 1) : d240898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202131, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202131, d240898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d26316 q = 1) (hb : d208034 q = 1) : d240912 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26316, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64602 q ha hb
    | true =>
      simp only [d26316, d240912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26317 q = 1) (hb : d208034 q = 1) : d240913 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26317, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26317, d240913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202132 q = 1) (hb : d208034 q = 1) : d240914 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202132, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202132, d240914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202133 q = 1) (hb : d208034 q = 1) : d240915 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202133, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202133, d240915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202134 q = 1) (hb : d208034 q = 1) : d240916 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202134, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202134, d240916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26324 q = 1) (hb : d208034 q = 1) : d240920 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26324, d240920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64604 q ha hb
    | true =>
      simp only [d26324, d240920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64605 q ha hb
  have h16 (q : Pattern) (ha : d26325 q = 1) (hb : d208034 q = 1) : d240921 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26325, d240921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26325, d240921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26326 q = 1) (hb : d208034 q = 1) : d240922 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26326, d240922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26326, d240922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26327 q = 1) (hb : d208034 q = 1) : d240923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26327, d240923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26327, d240923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d26330 q = 1) (hb : d208034 q = 1) : d240926 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26330, d240926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64606 q ha hb
    | true =>
      simp only [d26330, d240926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64607 q ha hb
  have h20 (q : Pattern) (ha : d26331 q = 1) (hb : d208034 q = 1) : d240927 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26331, d240927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26331, d240927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d26332 q = 1) (hb : d208034 q = 1) : d240928 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26332, d240928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d26332, d240928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d26334 q = 1) (hb : d208034 q = 1) : d240930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26334, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64608 q ha hb
    | true =>
      simp only [d26334, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64579 q ha hb
  have h23 (q : Pattern) (ha : d202136 q = 1) (hb : d208034 q = 1) : d240931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202136, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d26340 q = 1) (hb : d208034 q = 1) : d240933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26340, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64609 q ha hb
    | true =>
      simp only [d26340, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d26341 q = 1) (hb : d208034 q = 1) : d240934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26341, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d26341, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202137 q = 1) (hb : d208034 q = 1) : d240935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202137, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202138 q = 1) (hb : d208034 q = 1) : d240936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202138, d240936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202138, d240936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202139 q = 1) (hb : d208034 q = 1) : d240937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202139, d240937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202139, d240937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202140 q = 1) (hb : d208034 q = 1) : d240938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202140, d240938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202140, d240938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro64611 (p : Pattern) (ha : d202147 p = 1) (hb : d208034 p = 1) : d240958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26334 q = 1) (hb : d208034 q = 1) : d240930 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26334, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64608 q ha hb
    | true =>
      simp only [d26334, d240930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64579 q ha hb
  have h2 (q : Pattern) (ha : d202136 q = 1) (hb : d208034 q = 1) : d240931 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202136, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202136, d240931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26340 q = 1) (hb : d208034 q = 1) : d240933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26340, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64609 q ha hb
    | true =>
      simp only [d26340, d240933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26341 q = 1) (hb : d208034 q = 1) : d240934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26341, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26341, d240934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202137 q = 1) (hb : d208034 q = 1) : d240935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202137, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202137, d240935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202145 q = 1) (hb : d208034 q = 1) : d240956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202145, d240956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202145, d240956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202146 q = 1) (hb : d208034 q = 1) : d240957 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202146, d240957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202146, d240957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202147 q = 1) (hb : d208034 q = 1) : d240958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202147, d240958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202147, d240958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64612 (p : Pattern) (ha : d26391 p = 1) (hb : d208034 p = 1) : d240971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26373 q = 1) (hb : d208034 q = 1) : d240966 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26373, d240966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26373, d240966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64594 q ha hb
  have h2 (q : Pattern) (ha : d26189 q = 1) (hb : d208034 q = 1) : d240879 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26189, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64594 q ha hb
    | true =>
      simp only [d26189, d240879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26374 q = 1) (hb : d208034 q = 1) : d240967 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26374, d240967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26374, d240967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26190 q = 1) (hb : d208034 q = 1) : d240880 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26190, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26190, d240880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26375 q = 1) (hb : d208034 q = 1) : d240968 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26375, d240968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26375, d240968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26376 q = 1) (hb : d208034 q = 1) : d240969 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26376, d240969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26376, d240969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26377 q = 1) (hb : d208034 q = 1) : d26382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26377, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26377, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64595 q ha hb
  have h8 (q : Pattern) (ha : d26194 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26194, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64595 q ha hb
    | true =>
      simp only [d26194, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26378 q = 1) (hb : d208034 q = 1) : d26383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26378, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26378, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26195 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26195, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26195, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26379 q = 1) (hb : d208034 q = 1) : d26384 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26379, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26379, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26380 q = 1) (hb : d208034 q = 1) : d26385 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26380, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26380, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26381 q = 1) (hb : d208034 q = 1) : d240970 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26381, d240970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26381, d240970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26390 q = 1) (hb : d208034 q = 1) : d26390 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26391 q = 1) (hb : d208034 q = 1) : d240971 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26391, d240971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26391, d240971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64613 (p : Pattern) (ha : d26406 p = 1) (hb : d208034 p = 1) : d240977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26392 q = 1) (hb : d208034 q = 1) : d26382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26392, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26392, d26382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64566 q ha hb
  have h2 (q : Pattern) (ha : d26083 q = 1) (hb : d208034 q = 1) : d26200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26083, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64566 q ha hb
    | true =>
      simp only [d26083, d26200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26393 q = 1) (hb : d208034 q = 1) : d26383 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26393, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26393, d26383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26084 q = 1) (hb : d208034 q = 1) : d26201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26084, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26084, d26201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26394 q = 1) (hb : d208034 q = 1) : d26384 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26394, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26394, d26384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26395 q = 1) (hb : d208034 q = 1) : d26385 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26395, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26395, d26385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26396 q = 1) (hb : d208034 q = 1) : d26386 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26396, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26396, d26386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64567 q ha hb
  have h8 (q : Pattern) (ha : d26093 q = 1) (hb : d208034 q = 1) : d26101 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26093, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64567 q ha hb
    | true =>
      simp only [d26093, d26101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26397 q = 1) (hb : d208034 q = 1) : d26387 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26397, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26397, d26387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26094 q = 1) (hb : d208034 q = 1) : d26102 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26094, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26094, d26102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26398 q = 1) (hb : d208034 q = 1) : d26388 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26398, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26398, d26388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26399 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26399, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26399, d26389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26400 q = 1) (hb : d208034 q = 1) : d26390 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26400, d26390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26400, d26390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26389 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26401 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
  have h16 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d26402 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d26403 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d26404 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d26405 q = 1) (hb : d208034 q = 1) : d240976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26405, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26405, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d26406 q = 1) (hb : d208034 q = 1) : d240977 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26406, d240977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26406, d240977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro64614 (p : Pattern) (ha : d26411 p = 1) (hb : d208034 p = 1) : d240982 p = 1 := by
  have h0 (q : Pattern) (ha : d26389 q = 1) (hb : d208034 q = 1) : d26389 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26401 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
  have h3 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26402 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26403 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26404 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26405 q = 1) (hb : d208034 q = 1) : d240976 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26405, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26405, d240976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d26410 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d26411 q = 1) (hb : d208034 q = 1) : d240982 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26411, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26411, d240982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64615 (p : Pattern) (ha : d26431 p = 1) (hb : d208034 p = 1) : d240993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26407 q = 1) (hb : d208034 q = 1) : d240978 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26407, d240978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64612 q ha hb
    | true =>
      simp only [d26407, d240978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64613 q ha hb
  have h2 (q : Pattern) (ha : d26408 q = 1) (hb : d208034 q = 1) : d240979 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26408, d240979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26408, d240979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26409 q = 1) (hb : d208034 q = 1) : d240980 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26409, d240980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26409, d240980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26412 q = 1) (hb : d208034 q = 1) : d240983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26412, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64613 q ha hb
    | true =>
      simp only [d26412, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64614 q ha hb
  have h5 (q : Pattern) (ha : d26413 q = 1) (hb : d208034 q = 1) : d240984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26413, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26413, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26414 q = 1) (hb : d208034 q = 1) : d240985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26414, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26414, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26415 q = 1) (hb : d208034 q = 1) : d240986 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26415, d240986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26415, d240986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26422 q = 1) (hb : d208034 q = 1) : d240983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26422, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64613 q ha hb
    | true =>
      simp only [d26422, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
  have h9 (q : Pattern) (ha : d26423 q = 1) (hb : d208034 q = 1) : d240984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26423, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26423, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26424 q = 1) (hb : d208034 q = 1) : d240985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26424, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26424, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26426 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
    | true =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64586 q ha hb
  have h12 (q : Pattern) (ha : d26427 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26428 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26429 q = 1) (hb : d208034 q = 1) : d240991 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26429, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26429, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26430 q = 1) (hb : d208034 q = 1) : d240992 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26430, d240992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26430, d240992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26431 q = 1) (hb : d208034 q = 1) : d240993 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26431, d240993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26431, d240993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro64616 (p : Pattern) (ha : d26436 p = 1) (hb : d208034 p = 1) : d240998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26422 q = 1) (hb : d208034 q = 1) : d240983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26422, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64613 q ha hb
    | true =>
      simp only [d26422, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
  have h2 (q : Pattern) (ha : d26423 q = 1) (hb : d208034 q = 1) : d240984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26423, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26423, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26424 q = 1) (hb : d208034 q = 1) : d240985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26424, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26424, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26426 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
    | true =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64586 q ha hb
  have h5 (q : Pattern) (ha : d26427 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26428 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26429 q = 1) (hb : d208034 q = 1) : d240991 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26429, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26429, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26434 q = 1) (hb : d208034 q = 1) : d240996 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26434, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26434, d240996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26435 q = 1) (hb : d208034 q = 1) : d240997 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26435, d240997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26435, d240997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26436 q = 1) (hb : d208034 q = 1) : d240998 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26436, d240998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26436, d240998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64617 (p : Pattern) (ha : d26442 p = 1) (hb : d208034 p = 1) : d241004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26432 q = 1) (hb : d208034 q = 1) : d240994 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26432, d240994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64615 q ha hb
    | true =>
      simp only [d26432, d240994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26433 q = 1) (hb : d208034 q = 1) : d240995 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26433, d240995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26433, d240995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26437 q = 1) (hb : d208034 q = 1) : d240999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26437, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64616 q ha hb
    | true =>
      simp only [d26437, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26438 q = 1) (hb : d208034 q = 1) : d241000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26438, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26438, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26439 q = 1) (hb : d208034 q = 1) : d241001 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26439, d241001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26439, d241001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26440 q = 1) (hb : d208034 q = 1) : d241002 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26440, d241002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26440, d241002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26441 q = 1) (hb : d208034 q = 1) : d241003 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26441, d241003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26441, d241003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26442 q = 1) (hb : d208034 q = 1) : d241004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26442, d241004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26442, d241004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64618 (p : Pattern) (ha : d26450 p = 1) (hb : d208034 p = 1) : d241012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26437 q = 1) (hb : d208034 q = 1) : d240999 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26437, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64616 q ha hb
    | true =>
      simp only [d26437, d240999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26438 q = 1) (hb : d208034 q = 1) : d241000 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26438, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26438, d241000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26445 q = 1) (hb : d208034 q = 1) : d241007 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26445, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64587 q ha hb
    | true =>
      simp only [d26445, d241007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26446 q = 1) (hb : d208034 q = 1) : d241008 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26446, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26446, d241008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26447 q = 1) (hb : d208034 q = 1) : d241009 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26447, d241009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26447, d241009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26448 q = 1) (hb : d208034 q = 1) : d241010 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26448, d241010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26448, d241010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26449 q = 1) (hb : d208034 q = 1) : d241011 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26449, d241011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26449, d241011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26450 q = 1) (hb : d208034 q = 1) : d241012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26450, d241012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26450, d241012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64619 (p : Pattern) (ha : d26505 p = 1) (hb : d208034 p = 1) : d241015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26401 q = 1) (hb : d208034 q = 1) : d240972 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26401, d240972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
  have h2 (q : Pattern) (ha : d26108 q = 1) (hb : d208034 q = 1) : d240809 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64568 q ha hb
    | true =>
      simp only [d26108, d240809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26402 q = 1) (hb : d208034 q = 1) : d240973 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26402, d240973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26109 q = 1) (hb : d208034 q = 1) : d240810 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26109, d240810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26403 q = 1) (hb : d208034 q = 1) : d240974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26403, d240974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26404 q = 1) (hb : d208034 q = 1) : d240975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26404, d240975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26410 q = 1) (hb : d208034 q = 1) : d240981 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26410, d240981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26505 q = 1) (hb : d208034 q = 1) : d241015 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26505, d241015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26505, d241015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64620 (p : Pattern) (ha : d26511 p = 1) (hb : d208034 p = 1) : d241021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26422 q = 1) (hb : d208034 q = 1) : d240983 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26422, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64613 q ha hb
    | true =>
      simp only [d26422, d240983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
  have h2 (q : Pattern) (ha : d26423 q = 1) (hb : d208034 q = 1) : d240984 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26423, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26423, d240984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26424 q = 1) (hb : d208034 q = 1) : d240985 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26424, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26424, d240985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26426 q = 1) (hb : d208034 q = 1) : d240988 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
    | true =>
      simp only [d26426, d240988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64586 q ha hb
  have h5 (q : Pattern) (ha : d26427 q = 1) (hb : d208034 q = 1) : d240989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26427, d240989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26428 q = 1) (hb : d208034 q = 1) : d240990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26428, d240990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26429 q = 1) (hb : d208034 q = 1) : d240991 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26429, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26429, d240991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26506 q = 1) (hb : d208034 q = 1) : d241016 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26506, d241016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64585 q ha hb
    | true =>
      simp only [d26506, d241016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64619 q ha hb
  have h9 (q : Pattern) (ha : d26507 q = 1) (hb : d208034 q = 1) : d241017 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26507, d241017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26507, d241017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26508 q = 1) (hb : d208034 q = 1) : d241018 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26508, d241018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26508, d241018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26509 q = 1) (hb : d208034 q = 1) : d241019 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26509, d241019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26509, d241019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26510 q = 1) (hb : d208034 q = 1) : d241020 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26510, d241020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26510, d241020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26511 q = 1) (hb : d208034 q = 1) : d241021 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26511, d241021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26511, d241021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro64621 (p : Pattern) (ha : d26517 p = 1) (hb : d208034 p = 1) : d241027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26512 q = 1) (hb : d208034 q = 1) : d241022 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26512, d241022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64620 q ha hb
    | true =>
      simp only [d26512, d241022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26513 q = 1) (hb : d208034 q = 1) : d241023 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26513, d241023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26513, d241023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26514 q = 1) (hb : d208034 q = 1) : d241024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26514, d241024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26514, d241024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26515 q = 1) (hb : d208034 q = 1) : d241025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26515, d241025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26515, d241025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26516 q = 1) (hb : d208034 q = 1) : d241026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26516, d241026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26516, d241026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26517 q = 1) (hb : d208034 q = 1) : d241027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26517, d241027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26517, d241027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64622 (p : Pattern) (ha : d202157 p = 1) (hb : d208034 p = 1) : d241033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26451 q = 1) (hb : d208034 q = 1) : d241013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26451, d241013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64617 q ha hb
    | true =>
      simp only [d26451, d241013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64618 q ha hb
  have h2 (q : Pattern) (ha : d202153 q = 1) (hb : d208034 q = 1) : d241014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202153, d241014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202153, d241014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26518 q = 1) (hb : d208034 q = 1) : d241028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26518, d241028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64621 q ha hb
    | true =>
      simp only [d26518, d241028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26519 q = 1) (hb : d208034 q = 1) : d241029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26519, d241029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26519, d241029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202154 q = 1) (hb : d208034 q = 1) : d241030 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202154, d241030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202154, d241030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202155 q = 1) (hb : d208034 q = 1) : d241031 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202155, d241031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202155, d241031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202156 q = 1) (hb : d208034 q = 1) : d241032 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202156, d241032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202156, d241032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202157 q = 1) (hb : d208034 q = 1) : d241033 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202157, d241033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202157, d241033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64623 (p : Pattern) (ha : d202163 p = 1) (hb : d208034 p = 1) : d241050 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26155 q = 1) (hb : d208034 q = 1) : d240848 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26155, d240848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26155, d240848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64578 q ha hb
  have h2 (q : Pattern) (ha : d26156 q = 1) (hb : d208034 q = 1) : d240849 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26156, d240849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26156, d240849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26165 q = 1) (hb : d208034 q = 1) : d240858 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26165, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64578 q ha hb
    | true =>
      simp only [d26165, d240858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64581 q ha hb
  have h4 (q : Pattern) (ha : d26166 q = 1) (hb : d208034 q = 1) : d240859 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26166, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26166, d240859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26167 q = 1) (hb : d208034 q = 1) : d240860 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d26167, d240860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26167, d240860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202141 q = 1) (hb : d208034 q = 1) : d240939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202141, d240939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64603 q ha hb
    | true =>
      simp only [d202141, d240939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64610 q ha hb
  have h7 (q : Pattern) (ha : d26359 q = 1) (hb : d208034 q = 1) : d240952 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26359, d240952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64582 q ha hb
    | true =>
      simp only [d26359, d240952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64583 q ha hb
  have h8 (q : Pattern) (ha : d202142 q = 1) (hb : d208034 q = 1) : d240953 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202142, d240953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202142, d240953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202143 q = 1) (hb : d208034 q = 1) : d240954 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202143, d240954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202143, d240954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202144 q = 1) (hb : d208034 q = 1) : d240955 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202144, d240955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202144, d240955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202148 q = 1) (hb : d208034 q = 1) : d240959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202148, d240959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202148, d240959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64611 q ha hb
  have h12 (q : Pattern) (ha : d26368 q = 1) (hb : d208034 q = 1) : d240961 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26368, d240961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26368, d240961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64584 q ha hb
  have h13 (q : Pattern) (ha : d202149 q = 1) (hb : d208034 q = 1) : d240962 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202149, d240962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202149, d240962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202150 q = 1) (hb : d208034 q = 1) : d240963 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202150, d240963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202150, d240963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202151 q = 1) (hb : d208034 q = 1) : d240964 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202151, d240964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202151, d240964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202152 q = 1) (hb : d208034 q = 1) : d240965 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202152, d240965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202152, d240965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202158 q = 1) (hb : d208034 q = 1) : d241034 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202158, d241034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202158, d241034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64622 q ha hb
  have h18 (q : Pattern) (ha : d26535 q = 1) (hb : d208034 q = 1) : d241045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26535, d241045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26535, d241045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64589 q ha hb
  have h19 (q : Pattern) (ha : d202159 q = 1) (hb : d208034 q = 1) : d241046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202159, d241046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202159, d241046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202160 q = 1) (hb : d208034 q = 1) : d241047 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202160, d241047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202160, d241047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202161 q = 1) (hb : d208034 q = 1) : d241048 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202161, d241048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202161, d241048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202162 q = 1) (hb : d208034 q = 1) : d241049 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202162, d241049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202162, d241049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202163 q = 1) (hb : d208034 q = 1) : d241050 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202163, d241050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202163, d241050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro64624 (p : Pattern) (ha : d202169 p = 1) (hb : d208034 p = 1) : d241056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202164 q = 1) (hb : d208034 q = 1) : d241051 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202164, d241051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202164, d241051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64623 q ha hb
  have h2 (q : Pattern) (ha : d202165 q = 1) (hb : d208034 q = 1) : d241052 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202165, d241052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202165, d241052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202166 q = 1) (hb : d208034 q = 1) : d241053 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202166, d241053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202166, d241053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202167 q = 1) (hb : d208034 q = 1) : d241054 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202167, d241054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202167, d241054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202168 q = 1) (hb : d208034 q = 1) : d241055 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202168, d241055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202168, d241055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202169 q = 1) (hb : d208034 q = 1) : d241056 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202169, d241056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202169, d241056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64625 (p : Pattern) (ha : d26550 p = 1) (hb : d208034 p = 1) : d26658 p = 1 := by
  have h0 (q : Pattern) (ha : d10042 q = 1) (hb : d152852 q = 1) : d10042 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26185 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26186 q = 1) (hb : d208034 q = 1) : d10043 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26186, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26186, d208034, d10043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26187 q = 1) (hb : d208034 q = 1) : d10044 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26187, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26187, d10044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10053 q = 1) (hb : d208034 q = 1) : d10053 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26550 q = 1) (hb : d208034 q = 1) : d26658 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26550, d26658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26550, d26658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64626 (p : Pattern) (ha : d26561 p = 1) (hb : d208034 p = 1) : d26567 p = 1 := by
  have h0 (q : Pattern) (ha : d10051 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26556 q = 1) (hb : d208034 q = 1) : d10052 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26556, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26556, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26557 q = 1) (hb : d208034 q = 1) : d10053 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26557, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26557, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26560 q = 1) (hb : d208034 q = 1) : d26560 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26561 q = 1) (hb : d208034 q = 1) : d26567 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26561, d26567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26561, d26567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64627 (p : Pattern) (ha : d26574 p = 1) (hb : d208034 p = 1) : d241060 p = 1 := by
  have h0 (q : Pattern) (ha : d26558 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26572 q = 1) (hb : d208034 q = 1) : d26559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26572, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26572, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26573 q = 1) (hb : d208034 q = 1) : d26560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26573, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26573, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1593 q = 1) (hb : d152852 q = 1) : d1593 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10131 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10132 q = 1) (hb : d208034 q = 1) : d1594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d208034, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10132, d208034, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d10133 q = 1) (hb : d208034 q = 1) : d1595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10133, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d26574 q = 1) (hb : d208034 q = 1) : d241060 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26574, d241060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26574, d241060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64628 (p : Pattern) (ha : d26580 p = 1) (hb : d208034 p = 1) : d241066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26551 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64625 q ha hb
    | true =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26552 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26553 q = 1) (hb : d208034 q = 1) : d26661 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26553, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26553, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26554 q = 1) (hb : d208034 q = 1) : d26662 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26554, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26554, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26562 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26562, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64626 q ha hb
    | true =>
      simp only [d26562, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26563 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26563, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26563, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26564 q = 1) (hb : d208034 q = 1) : d26570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26564, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26564, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26565 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26565, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26565, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26566 q = 1) (hb : d208034 q = 1) : d26663 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26566, d26663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26566, d26663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26571 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26577 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26578 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26579 q = 1) (hb : d208034 q = 1) : d241065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26579, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26579, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26580 q = 1) (hb : d208034 q = 1) : d241066 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26580, d241066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26580, d241066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro64629 (p : Pattern) (ha : d26583 p = 1) (hb : d208034 p = 1) : d26567 p = 1 := by
  have h0 (q : Pattern) (ha : d10051 q = 1) (hb : d152852 q = 1) : d10051 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d26555 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26556 q = 1) (hb : d208034 q = 1) : d10052 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26556, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26556, d208034, d10052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26557 q = 1) (hb : d208034 q = 1) : d10053 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26557, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26557, d10053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26558 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d25767 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26581 q = 1) (hb : d208034 q = 1) : d26559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26581, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26581, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d26582 q = 1) (hb : d208034 q = 1) : d26560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26582, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26582, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d26583 q = 1) (hb : d208034 q = 1) : d26567 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26583, d26567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26583, d26567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64630 (p : Pattern) (ha : d26590 p = 1) (hb : d208034 p = 1) : d241068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26584 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64629 q ha hb
    | true =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26585 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26586 q = 1) (hb : d208034 q = 1) : d26570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26586, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26586, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26587 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26587, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26587, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26577 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26578 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26588 q = 1) (hb : d208034 q = 1) : d241065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26588, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26588, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26589 q = 1) (hb : d208034 q = 1) : d241067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26589, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26589, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26590 q = 1) (hb : d208034 q = 1) : d241068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26590, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26590, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64631 (p : Pattern) (ha : d10134 p = 1) (hb : d208034 p = 1) : d1596 p = 1 := by
  have h0 (q : Pattern) (ha : d1593 q = 1) (hb : d152852 q = 1) : d1593 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10132 q = 1) (hb : d208034 q = 1) : d1594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d208034, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10132, d208034, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10133 q = 1) (hb : d208034 q = 1) : d1595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10133, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10134 q = 1) (hb : d208034 q = 1) : d1596 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10134, d1596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10134, d1596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro64632 (p : Pattern) (ha : d26594 p = 1) (hb : d208034 p = 1) : d241072 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26577 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26578 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26589 q = 1) (hb : d208034 q = 1) : d241067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26589, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26589, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d208034 q = 1) : d1597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64631 q ha hb
    | true =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d208034 q = 1) : d1598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d208034 q = 1) : d1599 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d1599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d1599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d208034 q = 1) : d1600 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d1600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d1600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d208034 q = 1) : d1601 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d1601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d1601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26594 q = 1) (hb : d208034 q = 1) : d241072 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26594, d241072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26594, d241072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64633 (p : Pattern) (ha : d26601 p = 1) (hb : d208034 p = 1) : d241079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26591 q = 1) (hb : d208034 q = 1) : d241069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26591, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64628 q ha hb
    | true =>
      simp only [d26591, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64630 q ha hb
  have h2 (q : Pattern) (ha : d26592 q = 1) (hb : d208034 q = 1) : d241070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26592, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26592, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26593 q = 1) (hb : d208034 q = 1) : d241071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26593, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26593, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26595 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64630 q ha hb
    | true =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64632 q ha hb
  have h5 (q : Pattern) (ha : d26596 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26597 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26598 q = 1) (hb : d208034 q = 1) : d241076 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26598, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26598, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26599 q = 1) (hb : d208034 q = 1) : d241077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26599, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26599, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26600 q = 1) (hb : d208034 q = 1) : d241078 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26600, d241078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26600, d241078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26601 q = 1) (hb : d208034 q = 1) : d241079 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26601, d241079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26601, d241079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64634 (p : Pattern) (ha : d26605 p = 1) (hb : d208034 p = 1) : d241083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26595 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64630 q ha hb
    | true =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64632 q ha hb
  have h2 (q : Pattern) (ha : d26596 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26597 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26599 q = 1) (hb : d208034 q = 1) : d241077 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26599, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26599, d241077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26604 q = 1) (hb : d208034 q = 1) : d241082 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26604, d241082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26604, d241082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26605 q = 1) (hb : d208034 q = 1) : d241083 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26605, d241083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26605, d241083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64635 (p : Pattern) (ha : d26611 p = 1) (hb : d208034 p = 1) : d241089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26610 q = 1) (hb : d208034 q = 1) : d241088 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26610, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26610, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26611 q = 1) (hb : d208034 q = 1) : d241089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26611, d241089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26611, d241089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64636 (p : Pattern) (ha : d26615 p = 1) (hb : d208034 p = 1) : d241093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26614 q = 1) (hb : d208034 q = 1) : d241092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26614, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26614, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26615 q = 1) (hb : d208034 q = 1) : d241093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26615, d241093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26615, d241093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64637 (p : Pattern) (ha : d26621 p = 1) (hb : d208034 p = 1) : d241099 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26616 q = 1) (hb : d208034 q = 1) : d241094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26616, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64635 q ha hb
    | true =>
      simp only [d26616, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64636 q ha hb
  have h2 (q : Pattern) (ha : d26617 q = 1) (hb : d208034 q = 1) : d241095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26617, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26617, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26618 q = 1) (hb : d208034 q = 1) : d241096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26618, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26618, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26619 q = 1) (hb : d208034 q = 1) : d241097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26619, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26619, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26620 q = 1) (hb : d208034 q = 1) : d241098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26620, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26620, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26621 q = 1) (hb : d208034 q = 1) : d241099 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26621, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26621, d241099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64638 (p : Pattern) (ha : d26624 p = 1) (hb : d208034 p = 1) : d241102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26610 q = 1) (hb : d208034 q = 1) : d241088 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26610, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26610, d241088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26624 q = 1) (hb : d208034 q = 1) : d241102 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26624, d241102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26624, d241102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64639 (p : Pattern) (ha : d26625 p = 1) (hb : d208034 p = 1) : d241103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26614 q = 1) (hb : d208034 q = 1) : d241092 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26614, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26614, d241092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26625 q = 1) (hb : d208034 q = 1) : d241103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26625, d241103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26625, d241103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64640 (p : Pattern) (ha : d26631 p = 1) (hb : d208034 p = 1) : d241109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26616 q = 1) (hb : d208034 q = 1) : d241094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26616, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64635 q ha hb
    | true =>
      simp only [d26616, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64636 q ha hb
  have h2 (q : Pattern) (ha : d26617 q = 1) (hb : d208034 q = 1) : d241095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26617, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26617, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26618 q = 1) (hb : d208034 q = 1) : d241096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26618, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26618, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26619 q = 1) (hb : d208034 q = 1) : d241097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26619, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26619, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26620 q = 1) (hb : d208034 q = 1) : d241098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26620, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26620, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26626 q = 1) (hb : d208034 q = 1) : d241104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26626, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64638 q ha hb
    | true =>
      simp only [d26626, d241104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64639 q ha hb
  have h7 (q : Pattern) (ha : d26627 q = 1) (hb : d208034 q = 1) : d241105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26627, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26627, d241105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26628 q = 1) (hb : d208034 q = 1) : d241106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26628, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26628, d241106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26629 q = 1) (hb : d208034 q = 1) : d241107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26629, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26629, d241107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26630 q = 1) (hb : d208034 q = 1) : d241108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26630, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26630, d241108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26631 q = 1) (hb : d208034 q = 1) : d241109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26631, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26631, d241109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64641 (p : Pattern) (ha : d26813 p = 1) (hb : d208034 p = 1) : d241199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26616 q = 1) (hb : d208034 q = 1) : d241094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26616, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64635 q ha hb
    | true =>
      simp only [d26616, d241094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64636 q ha hb
  have h2 (q : Pattern) (ha : d26617 q = 1) (hb : d208034 q = 1) : d241095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26617, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26617, d241095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26618 q = 1) (hb : d208034 q = 1) : d241096 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26618, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26618, d241096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26619 q = 1) (hb : d208034 q = 1) : d241097 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26619, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26619, d241097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26620 q = 1) (hb : d208034 q = 1) : d241098 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26620, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26620, d241098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26808 q = 1) (hb : d208034 q = 1) : d241194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26808, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64636 q ha hb
    | true =>
      simp only [d26808, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26809 q = 1) (hb : d208034 q = 1) : d241195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26809, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26809, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26810 q = 1) (hb : d208034 q = 1) : d241196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26810, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26810, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26811 q = 1) (hb : d208034 q = 1) : d241197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26811, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26811, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26812 q = 1) (hb : d208034 q = 1) : d241198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26812, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26812, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26813 q = 1) (hb : d208034 q = 1) : d241199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26813, d241199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26813, d241199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64642 (p : Pattern) (ha : d26819 p = 1) (hb : d208034 p = 1) : d241205 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26808 q = 1) (hb : d208034 q = 1) : d241194 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26808, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64636 q ha hb
    | true =>
      simp only [d26808, d241194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26809 q = 1) (hb : d208034 q = 1) : d241195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26809, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26809, d241195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26810 q = 1) (hb : d208034 q = 1) : d241196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26810, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26810, d241196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26811 q = 1) (hb : d208034 q = 1) : d241197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26811, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26811, d241197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26812 q = 1) (hb : d208034 q = 1) : d241198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26812, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26812, d241198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26814 q = 1) (hb : d208034 q = 1) : d241200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26814, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64639 q ha hb
    | true =>
      simp only [d26814, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26815 q = 1) (hb : d208034 q = 1) : d241201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26815, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26815, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26816 q = 1) (hb : d208034 q = 1) : d241202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26816, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26816, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26817 q = 1) (hb : d208034 q = 1) : d241203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26817, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26817, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26818 q = 1) (hb : d208034 q = 1) : d241204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26818, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26818, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26819 q = 1) (hb : d208034 q = 1) : d241205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26819, d241205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26819, d241205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64643 (p : Pattern) (ha : d26828 p = 1) (hb : d208034 p = 1) : d241214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26814 q = 1) (hb : d208034 q = 1) : d241200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26814, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64639 q ha hb
    | true =>
      simp only [d26814, d241200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26815 q = 1) (hb : d208034 q = 1) : d241201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26815, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26815, d241201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26816 q = 1) (hb : d208034 q = 1) : d241202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26816, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26816, d241202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26817 q = 1) (hb : d208034 q = 1) : d241203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26817, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26817, d241203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26818 q = 1) (hb : d208034 q = 1) : d241204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26818, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26818, d241204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26828 q = 1) (hb : d208034 q = 1) : d241214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26828, d241214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26828, d241214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64644 (p : Pattern) (ha : d26878 p = 1) (hb : d208034 p = 1) : d241232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26873 q = 1) (hb : d208034 q = 1) : d26847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26873, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26873, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64629 q ha hb
  have h2 (q : Pattern) (ha : d26584 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64629 q ha hb
    | true =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26874 q = 1) (hb : d208034 q = 1) : d26848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26874, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26874, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26585 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26875 q = 1) (hb : d208034 q = 1) : d26849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26875, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26875, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26876 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26876, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26876, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26858 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
  have h8 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26859 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26860 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26861 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26877 q = 1) (hb : d208034 q = 1) : d241226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26877, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26877, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26867 q = 1) (hb : d208034 q = 1) : d241231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26867, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26867, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26878 q = 1) (hb : d208034 q = 1) : d241232 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26878, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26878, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64645 (p : Pattern) (ha : d26882 p = 1) (hb : d208034 p = 1) : d241237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26858 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
  have h2 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26859 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26860 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26861 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26867 q = 1) (hb : d208034 q = 1) : d241231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26867, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26867, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d208034 q = 1) : d1883 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d1883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d1883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64631 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d208034 q = 1) : d1597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64631 q ha hb
    | true =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d208034 q = 1) : d1884 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d1884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d1884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d208034 q = 1) : d1598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d208034 q = 1) : d1885 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d1885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d1885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d208034 q = 1) : d1886 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d1886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d1886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d208034 q = 1) : d1887 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d1887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d1887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26882 q = 1) (hb : d208034 q = 1) : d241237 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26882, d241237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26882, d241237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64646 (p : Pattern) (ha : d26901 p = 1) (hb : d208034 p = 1) : d241256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26883 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64644 q ha hb
    | true =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64645 q ha hb
  have h2 (q : Pattern) (ha : d26884 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26885 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26891 q = 1) (hb : d208034 q = 1) : d241246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26891, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26891, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26900 q = 1) (hb : d208034 q = 1) : d241255 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26900, d241255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26900, d241255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26901 q = 1) (hb : d208034 q = 1) : d241256 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26901, d241256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26901, d241256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64647 (p : Pattern) (ha : d26991 p = 1) (hb : d208034 p = 1) : d241294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26902 q = 1) (hb : d208034 q = 1) : d241257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26902, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64646 q ha hb
    | true =>
      simp only [d26902, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26903 q = 1) (hb : d208034 q = 1) : d241258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26903, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26903, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26988 q = 1) (hb : d208034 q = 1) : d241291 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26988, d241291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26988, d241291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26989 q = 1) (hb : d208034 q = 1) : d241292 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26989, d241292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26989, d241292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26990 q = 1) (hb : d208034 q = 1) : d241293 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26990, d241293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26990, d241293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26991 q = 1) (hb : d208034 q = 1) : d241294 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26991, d241294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26991, d241294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64648 (p : Pattern) (ha : d26997 p = 1) (hb : d208034 p = 1) : d241300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26992 q = 1) (hb : d208034 q = 1) : d241295 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26992, d241295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64647 q ha hb
    | true =>
      simp only [d26992, d241295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26993 q = 1) (hb : d208034 q = 1) : d241296 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26993, d241296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26993, d241296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26994 q = 1) (hb : d208034 q = 1) : d241297 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26994, d241297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26994, d241297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26995 q = 1) (hb : d208034 q = 1) : d241298 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26995, d241298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26995, d241298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26996 q = 1) (hb : d208034 q = 1) : d241299 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d26996, d241299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26996, d241299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26997 q = 1) (hb : d208034 q = 1) : d241300 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d26997, d241300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26997, d241300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64649 (p : Pattern) (ha : d26636 p = 1) (hb : d208034 p = 1) : d241114 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26635 q = 1) (hb : d208034 q = 1) : d241113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26635, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26635, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26636 q = 1) (hb : d208034 q = 1) : d241114 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26636, d241114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26636, d241114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64650 (p : Pattern) (ha : d26638 p = 1) (hb : d208034 p = 1) : d241116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26637 q = 1) (hb : d208034 q = 1) : d241115 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26637, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26637, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26638 q = 1) (hb : d208034 q = 1) : d241116 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26638, d241116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26638, d241116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64651 (p : Pattern) (ha : d26645 p = 1) (hb : d208034 p = 1) : d241123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26643 q = 1) (hb : d208034 q = 1) : d241121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26643, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26643, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26644 q = 1) (hb : d208034 q = 1) : d241122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26644, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26644, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26645 q = 1) (hb : d208034 q = 1) : d241123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26645, d241123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26645, d241123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64652 (p : Pattern) (ha : d26648 p = 1) (hb : d208034 p = 1) : d241126 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26646 q = 1) (hb : d208034 q = 1) : d241124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26646, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26646, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26647 q = 1) (hb : d208034 q = 1) : d241125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26647, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26647, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26648 q = 1) (hb : d208034 q = 1) : d241126 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26648, d241126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26648, d241126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64653 (p : Pattern) (ha : d26664 p = 1) (hb : d208034 p = 1) : d241131 p = 1 := by
  have h0 (q : Pattern) (ha : d26656 q = 1) (hb : d208034 q = 1) : d26656 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26551 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64625 q ha hb
    | true =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26552 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26553 q = 1) (hb : d208034 q = 1) : d26661 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26553, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26553, d26661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26554 q = 1) (hb : d208034 q = 1) : d26662 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26554, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26554, d26662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26657 q = 1) (hb : d208034 q = 1) : d241130 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26657, d241130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26657, d241130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26663 q = 1) (hb : d208034 q = 1) : d26663 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d26664 q = 1) (hb : d208034 q = 1) : d241131 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26664, d241131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26664, d241131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64654 (p : Pattern) (ha : d26668 p = 1) (hb : d208034 p = 1) : d241068 p = 1 := by
  have h0 (q : Pattern) (ha : d26571 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26577 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26578 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26579 q = 1) (hb : d208034 q = 1) : d241065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26579, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26579, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26589 q = 1) (hb : d208034 q = 1) : d241067 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26589, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26589, d241067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26668 q = 1) (hb : d208034 q = 1) : d241068 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26668, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26668, d241068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64655 (p : Pattern) (ha : d26674 p = 1) (hb : d208034 p = 1) : d241137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26665 q = 1) (hb : d208034 q = 1) : d241132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26665, d241132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64653 q ha hb
    | true =>
      simp only [d26665, d241132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64628 q ha hb
  have h2 (q : Pattern) (ha : d26666 q = 1) (hb : d208034 q = 1) : d241133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26666, d241133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26666, d241133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26667 q = 1) (hb : d208034 q = 1) : d241134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26667, d241134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26667, d241134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26669 q = 1) (hb : d208034 q = 1) : d241069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26669, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64628 q ha hb
    | true =>
      simp only [d26669, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64654 q ha hb
  have h5 (q : Pattern) (ha : d26670 q = 1) (hb : d208034 q = 1) : d241070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26670, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26670, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26671 q = 1) (hb : d208034 q = 1) : d241071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26671, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26671, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26672 q = 1) (hb : d208034 q = 1) : d241135 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26672, d241135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26672, d241135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26591 q = 1) (hb : d208034 q = 1) : d241069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26591, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64628 q ha hb
    | true =>
      simp only [d26591, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64630 q ha hb
  have h9 (q : Pattern) (ha : d26592 q = 1) (hb : d208034 q = 1) : d241070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26592, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26592, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26593 q = 1) (hb : d208034 q = 1) : d241071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26593, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26593, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26595 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64630 q ha hb
    | true =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64632 q ha hb
  have h12 (q : Pattern) (ha : d26596 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26597 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26598 q = 1) (hb : d208034 q = 1) : d241076 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26598, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26598, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26673 q = 1) (hb : d208034 q = 1) : d241136 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26673, d241136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26673, d241136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26674 q = 1) (hb : d208034 q = 1) : d241137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26674, d241137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26674, d241137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro64656 (p : Pattern) (ha : d26680 p = 1) (hb : d208034 p = 1) : d241143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26675 q = 1) (hb : d208034 q = 1) : d241138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26675, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64655 q ha hb
    | true =>
      simp only [d26675, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26676 q = 1) (hb : d208034 q = 1) : d241139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26676, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26676, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26677 q = 1) (hb : d208034 q = 1) : d241140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26677, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26677, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26678 q = 1) (hb : d208034 q = 1) : d241141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26678, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26678, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26679 q = 1) (hb : d208034 q = 1) : d241142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26679, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26679, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26680 q = 1) (hb : d208034 q = 1) : d241143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26680, d241143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26680, d241143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64657 (p : Pattern) (ha : d26757 p = 1) (hb : d208034 p = 1) : d241146 p = 1 := by
  have h0 (q : Pattern) (ha : d26558 q = 1) (hb : d152852 q = 1) : d26558 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26572 q = 1) (hb : d208034 q = 1) : d26559 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26572, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26572, d208034, d26559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d26573 q = 1) (hb : d208034 q = 1) : d26560 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26573, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26573, d26560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26754 q = 1) (hb : d152852 q = 1) : d26754 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1578 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d26755 q = 1) (hb : d208034 q = 1) : d239545 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26755, d208034, d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26755, d208034, d239545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d26756 q = 1) (hb : d208034 q = 1) : d239546 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26756, d239546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26756, d239546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d26757 q = 1) (hb : d208034 q = 1) : d241146 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d26757, d241146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26757, d241146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64658 (p : Pattern) (ha : d26763 p = 1) (hb : d208034 p = 1) : d241152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26584 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64629 q ha hb
    | true =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26585 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26586 q = 1) (hb : d208034 q = 1) : d26570 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26586, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26586, d26570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26587 q = 1) (hb : d208034 q = 1) : d26571 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26587, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26587, d26571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26577 q = 1) (hb : d208034 q = 1) : d241063 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26577, d241063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26578 q = 1) (hb : d208034 q = 1) : d241064 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26578, d241064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26588 q = 1) (hb : d208034 q = 1) : d241065 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26588, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26588, d241065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26758 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64657 q ha hb
    | true =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26759 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26760 q = 1) (hb : d208034 q = 1) : d241149 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26760, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26760, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26761 q = 1) (hb : d208034 q = 1) : d241150 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26761, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26761, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d26762 q = 1) (hb : d208034 q = 1) : d241151 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26762, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26762, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d26763 q = 1) (hb : d208034 q = 1) : d241152 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26763, d241152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26763, d241152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64659 (p : Pattern) (ha : d26764 p = 1) (hb : d208034 p = 1) : d241153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26758 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64657 q ha hb
    | true =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26759 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26760 q = 1) (hb : d208034 q = 1) : d241149 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26760, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26760, d241149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26761 q = 1) (hb : d208034 q = 1) : d241150 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26761, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26761, d241150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26762 q = 1) (hb : d208034 q = 1) : d241151 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26762, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26762, d241151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26764 q = 1) (hb : d208034 q = 1) : d241153 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26764, d241153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26764, d241153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64660 (p : Pattern) (ha : d26770 p = 1) (hb : d208034 p = 1) : d241159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26591 q = 1) (hb : d208034 q = 1) : d241069 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26591, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64628 q ha hb
    | true =>
      simp only [d26591, d241069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64630 q ha hb
  have h2 (q : Pattern) (ha : d26592 q = 1) (hb : d208034 q = 1) : d241070 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26592, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26592, d241070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26593 q = 1) (hb : d208034 q = 1) : d241071 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26593, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26593, d241071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26595 q = 1) (hb : d208034 q = 1) : d241073 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64630 q ha hb
    | true =>
      simp only [d26595, d241073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64632 q ha hb
  have h5 (q : Pattern) (ha : d26596 q = 1) (hb : d208034 q = 1) : d241074 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26596, d241074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26597 q = 1) (hb : d208034 q = 1) : d241075 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26597, d241075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26598 q = 1) (hb : d208034 q = 1) : d241076 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26598, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26598, d241076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26765 q = 1) (hb : d208034 q = 1) : d241154 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26765, d241154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64658 q ha hb
    | true =>
      simp only [d26765, d241154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64659 q ha hb
  have h9 (q : Pattern) (ha : d26766 q = 1) (hb : d208034 q = 1) : d241155 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26766, d241155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26766, d241155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26767 q = 1) (hb : d208034 q = 1) : d241156 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26767, d241156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26767, d241156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26768 q = 1) (hb : d208034 q = 1) : d241157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26768, d241157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26768, d241157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26769 q = 1) (hb : d208034 q = 1) : d241158 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26769, d241158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26769, d241158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26770 q = 1) (hb : d208034 q = 1) : d241159 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26770, d241159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26770, d241159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro64661 (p : Pattern) (ha : d26776 p = 1) (hb : d208034 p = 1) : d241165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26771 q = 1) (hb : d208034 q = 1) : d241160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26771, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64660 q ha hb
    | true =>
      simp only [d26771, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26772 q = 1) (hb : d208034 q = 1) : d241161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26772, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26772, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26773 q = 1) (hb : d208034 q = 1) : d241162 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26773, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26773, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26774 q = 1) (hb : d208034 q = 1) : d241163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26774, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26774, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26775 q = 1) (hb : d208034 q = 1) : d241164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26775, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26775, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26776 q = 1) (hb : d208034 q = 1) : d241165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26776, d241165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26776, d241165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64662 (p : Pattern) (ha : d202177 p = 1) (hb : d208034 p = 1) : d241171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26639 q = 1) (hb : d208034 q = 1) : d241117 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26639, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64649 q ha hb
    | true =>
      simp only [d26639, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64650 q ha hb
  have h2 (q : Pattern) (ha : d26640 q = 1) (hb : d208034 q = 1) : d241118 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26640, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26640, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26641 q = 1) (hb : d208034 q = 1) : d241119 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26641, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26641, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26642 q = 1) (hb : d208034 q = 1) : d241120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26642, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26642, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26649 q = 1) (hb : d208034 q = 1) : d241127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26649, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64651 q ha hb
    | true =>
      simp only [d26649, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64652 q ha hb
  have h6 (q : Pattern) (ha : d26650 q = 1) (hb : d208034 q = 1) : d241128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26650, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26650, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26651 q = 1) (hb : d208034 q = 1) : d241129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26651, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26651, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26681 q = 1) (hb : d208034 q = 1) : d241144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26681, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64656 q ha hb
    | true =>
      simp only [d26681, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64635 q ha hb
  have h9 (q : Pattern) (ha : d202173 q = 1) (hb : d208034 q = 1) : d241145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202173, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d26777 q = 1) (hb : d208034 q = 1) : d241166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26777, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64661 q ha hb
    | true =>
      simp only [d26777, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26778 q = 1) (hb : d208034 q = 1) : d241167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26778, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26778, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202174 q = 1) (hb : d208034 q = 1) : d241168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202174, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202175 q = 1) (hb : d208034 q = 1) : d241169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202175, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202176 q = 1) (hb : d208034 q = 1) : d241170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202176, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202177 q = 1) (hb : d208034 q = 1) : d241171 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202177, d241171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202177, d241171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64663 (p : Pattern) (ha : d26783 p = 1) (hb : d208034 p = 1) : d241172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26609 q = 1) (hb : d208034 q = 1) : d241087 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26609, d241087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26635 q = 1) (hb : d208034 q = 1) : d241113 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26635, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26635, d241113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26783 q = 1) (hb : d208034 q = 1) : d241172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26783, d241172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26783, d241172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64664 (p : Pattern) (ha : d26784 p = 1) (hb : d208034 p = 1) : d241173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26613 q = 1) (hb : d208034 q = 1) : d241091 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26613, d241091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26637 q = 1) (hb : d208034 q = 1) : d241115 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26637, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26637, d241115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26784 q = 1) (hb : d208034 q = 1) : d241173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26784, d241173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26784, d241173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64665 (p : Pattern) (ha : d26789 p = 1) (hb : d208034 p = 1) : d241178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26608 q = 1) (hb : d208034 q = 1) : d241086 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26608, d241086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26643 q = 1) (hb : d208034 q = 1) : d241121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26643, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26643, d241121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26644 q = 1) (hb : d208034 q = 1) : d241122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26644, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26644, d241122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26789 q = 1) (hb : d208034 q = 1) : d241178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26789, d241178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26789, d241178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64666 (p : Pattern) (ha : d26790 p = 1) (hb : d208034 p = 1) : d241179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26606 q = 1) (hb : d208034 q = 1) : d241084 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64634 q ha hb
    | true =>
      simp only [d26606, d241084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26607 q = 1) (hb : d208034 q = 1) : d241085 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26607, d241085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26612 q = 1) (hb : d208034 q = 1) : d241090 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26612, d241090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26646 q = 1) (hb : d208034 q = 1) : d241124 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26646, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26646, d241124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26647 q = 1) (hb : d208034 q = 1) : d241125 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26647, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26647, d241125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26790 q = 1) (hb : d208034 q = 1) : d241179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26790, d241179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26790, d241179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64667 (p : Pattern) (ha : d26794 p = 1) (hb : d208034 p = 1) : d241183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26675 q = 1) (hb : d208034 q = 1) : d241138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26675, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64655 q ha hb
    | true =>
      simp only [d26675, d241138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26676 q = 1) (hb : d208034 q = 1) : d241139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26676, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26676, d241139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26602 q = 1) (hb : d208034 q = 1) : d241080 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64633 q ha hb
    | true =>
      simp only [d26602, d241080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26603 q = 1) (hb : d208034 q = 1) : d241081 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26603, d241081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26677 q = 1) (hb : d208034 q = 1) : d241140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26677, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26677, d241140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26678 q = 1) (hb : d208034 q = 1) : d241141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26678, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26678, d241141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26679 q = 1) (hb : d208034 q = 1) : d241142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26679, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26679, d241142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26794 q = 1) (hb : d208034 q = 1) : d241183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26794, d241183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26794, d241183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64668 (p : Pattern) (ha : d26800 p = 1) (hb : d208034 p = 1) : d241186 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26771 q = 1) (hb : d208034 q = 1) : d241160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26771, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64660 q ha hb
    | true =>
      simp only [d26771, d241160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26772 q = 1) (hb : d208034 q = 1) : d241161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26772, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26772, d241161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26773 q = 1) (hb : d208034 q = 1) : d241162 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26773, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26773, d241162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26774 q = 1) (hb : d208034 q = 1) : d241163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26774, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26774, d241163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26775 q = 1) (hb : d208034 q = 1) : d241164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26775, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26775, d241164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26800 q = 1) (hb : d208034 q = 1) : d241186 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26800, d241186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26800, d241186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64669 (p : Pattern) (ha : d202182 p = 1) (hb : d208034 p = 1) : d241192 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26639 q = 1) (hb : d208034 q = 1) : d241117 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26639, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64649 q ha hb
    | true =>
      simp only [d26639, d241117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64650 q ha hb
  have h2 (q : Pattern) (ha : d26640 q = 1) (hb : d208034 q = 1) : d241118 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26640, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26640, d241118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26641 q = 1) (hb : d208034 q = 1) : d241119 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26641, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26641, d241119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26642 q = 1) (hb : d208034 q = 1) : d241120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26642, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26642, d241120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26649 q = 1) (hb : d208034 q = 1) : d241127 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26649, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64651 q ha hb
    | true =>
      simp only [d26649, d241127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64652 q ha hb
  have h6 (q : Pattern) (ha : d26650 q = 1) (hb : d208034 q = 1) : d241128 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26650, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26650, d241128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26651 q = 1) (hb : d208034 q = 1) : d241129 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26651, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26651, d241129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26681 q = 1) (hb : d208034 q = 1) : d241144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26681, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64656 q ha hb
    | true =>
      simp only [d26681, d241144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64635 q ha hb
  have h9 (q : Pattern) (ha : d202173 q = 1) (hb : d208034 q = 1) : d241145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202173, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202173, d241145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d26777 q = 1) (hb : d208034 q = 1) : d241166 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26777, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64661 q ha hb
    | true =>
      simp only [d26777, d241166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26778 q = 1) (hb : d208034 q = 1) : d241167 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26778, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26778, d241167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202174 q = 1) (hb : d208034 q = 1) : d241168 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202174, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202174, d241168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202175 q = 1) (hb : d208034 q = 1) : d241169 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202175, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202175, d241169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202176 q = 1) (hb : d208034 q = 1) : d241170 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202176, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202176, d241170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26785 q = 1) (hb : d208034 q = 1) : d241174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26785, d241174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64663 q ha hb
    | true =>
      simp only [d26785, d241174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64664 q ha hb
  have h16 (q : Pattern) (ha : d26786 q = 1) (hb : d208034 q = 1) : d241175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26786, d241175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26786, d241175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26787 q = 1) (hb : d208034 q = 1) : d241176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26787, d241176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26787, d241176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26788 q = 1) (hb : d208034 q = 1) : d241177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d26788, d241177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26788, d241177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d26791 q = 1) (hb : d208034 q = 1) : d241180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26791, d241180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64665 q ha hb
    | true =>
      simp only [d26791, d241180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64666 q ha hb
  have h20 (q : Pattern) (ha : d26792 q = 1) (hb : d208034 q = 1) : d241181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26792, d241181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26792, d241181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d26793 q = 1) (hb : d208034 q = 1) : d241182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d26793, d241182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d26793, d241182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d26795 q = 1) (hb : d208034 q = 1) : d241184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26795, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64667 q ha hb
    | true =>
      simp only [d26795, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64638 q ha hb
  have h23 (q : Pattern) (ha : d202178 q = 1) (hb : d208034 q = 1) : d241185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202178, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d26801 q = 1) (hb : d208034 q = 1) : d241187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26801, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64668 q ha hb
    | true =>
      simp only [d26801, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d26802 q = 1) (hb : d208034 q = 1) : d241188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26802, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d26802, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202179 q = 1) (hb : d208034 q = 1) : d241189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202179, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202180 q = 1) (hb : d208034 q = 1) : d241190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202180, d241190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202180, d241190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202181 q = 1) (hb : d208034 q = 1) : d241191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202181, d241191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202181, d241191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202182 q = 1) (hb : d208034 q = 1) : d241192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202182, d241192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202182, d241192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro64670 (p : Pattern) (ha : d202189 p = 1) (hb : d208034 p = 1) : d241212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26795 q = 1) (hb : d208034 q = 1) : d241184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26795, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64667 q ha hb
    | true =>
      simp only [d26795, d241184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64638 q ha hb
  have h2 (q : Pattern) (ha : d202178 q = 1) (hb : d208034 q = 1) : d241185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202178, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202178, d241185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26801 q = 1) (hb : d208034 q = 1) : d241187 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26801, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64668 q ha hb
    | true =>
      simp only [d26801, d241187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26802 q = 1) (hb : d208034 q = 1) : d241188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26802, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26802, d241188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202179 q = 1) (hb : d208034 q = 1) : d241189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202179, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202179, d241189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202187 q = 1) (hb : d208034 q = 1) : d241210 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202187, d241210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202187, d241210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202188 q = 1) (hb : d208034 q = 1) : d241211 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202188, d241211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202188, d241211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202189 q = 1) (hb : d208034 q = 1) : d241212 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202189, d241212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202189, d241212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64671 (p : Pattern) (ha : d26852 p = 1) (hb : d208034 p = 1) : d241221 p = 1 := by
  have h0 (q : Pattern) (ha : d26837 q = 1) (hb : d208034 q = 1) : d26837 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26838 q = 1) (hb : d208034 q = 1) : d26843 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26838, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26838, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64625 q ha hb
  have h3 (q : Pattern) (ha : d26551 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64625 q ha hb
    | true =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26839 q = 1) (hb : d208034 q = 1) : d26844 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26839, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26839, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26552 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26840 q = 1) (hb : d208034 q = 1) : d26845 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26840, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26840, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26841 q = 1) (hb : d208034 q = 1) : d26846 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26841, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26841, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26842 q = 1) (hb : d208034 q = 1) : d241220 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26842, d241220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26842, d241220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d26851 q = 1) (hb : d208034 q = 1) : d26851 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d26852 q = 1) (hb : d208034 q = 1) : d241221 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26852, d241221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26852, d241221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64672 (p : Pattern) (ha : d26863 p = 1) (hb : d208034 p = 1) : d241227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26838 q = 1) (hb : d208034 q = 1) : d26843 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26838, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26838, d26843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64625 q ha hb
  have h2 (q : Pattern) (ha : d26551 q = 1) (hb : d208034 q = 1) : d26659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64625 q ha hb
    | true =>
      simp only [d26551, d26659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26839 q = 1) (hb : d208034 q = 1) : d26844 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26839, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26839, d26844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26552 q = 1) (hb : d208034 q = 1) : d26660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26552, d26660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26840 q = 1) (hb : d208034 q = 1) : d26845 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26840, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26840, d26845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26841 q = 1) (hb : d208034 q = 1) : d26846 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26841, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26841, d26846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26853 q = 1) (hb : d208034 q = 1) : d26847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26853, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26853, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64626 q ha hb
  have h8 (q : Pattern) (ha : d26562 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26562, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64626 q ha hb
    | true =>
      simp only [d26562, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26854 q = 1) (hb : d208034 q = 1) : d26848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26854, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26854, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26563 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26563, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26563, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26855 q = 1) (hb : d208034 q = 1) : d26849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26855, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26855, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26856 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26856, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26856, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26857 q = 1) (hb : d208034 q = 1) : d26851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26857, d26851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26857, d26851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26850 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d26858 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
  have h16 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d26859 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d26860 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d26861 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d26862 q = 1) (hb : d208034 q = 1) : d241226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26862, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26862, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d26863 q = 1) (hb : d208034 q = 1) : d241227 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26863, d241227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26863, d241227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro64673 (p : Pattern) (ha : d26868 p = 1) (hb : d208034 p = 1) : d241232 p = 1 := by
  have h0 (q : Pattern) (ha : d26850 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d26858 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
  have h3 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d26859 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d26860 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26861 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d26862 q = 1) (hb : d208034 q = 1) : d241226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26862, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26862, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d26867 q = 1) (hb : d208034 q = 1) : d241231 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26867, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26867, d241231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d26868 q = 1) (hb : d208034 q = 1) : d241232 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26868, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26868, d241232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64674 (p : Pattern) (ha : d26888 p = 1) (hb : d208034 p = 1) : d241243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26864 q = 1) (hb : d208034 q = 1) : d241228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26864, d241228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64671 q ha hb
    | true =>
      simp only [d26864, d241228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64672 q ha hb
  have h2 (q : Pattern) (ha : d26865 q = 1) (hb : d208034 q = 1) : d241229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26865, d241229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26865, d241229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26866 q = 1) (hb : d208034 q = 1) : d241230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26866, d241230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26866, d241230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26869 q = 1) (hb : d208034 q = 1) : d241233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26869, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64672 q ha hb
    | true =>
      simp only [d26869, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64673 q ha hb
  have h5 (q : Pattern) (ha : d26870 q = 1) (hb : d208034 q = 1) : d241234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26870, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26870, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26871 q = 1) (hb : d208034 q = 1) : d241235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26871, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26871, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26872 q = 1) (hb : d208034 q = 1) : d241236 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26872, d241236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26872, d241236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26879 q = 1) (hb : d208034 q = 1) : d241233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26879, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64672 q ha hb
    | true =>
      simp only [d26879, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64644 q ha hb
  have h9 (q : Pattern) (ha : d26880 q = 1) (hb : d208034 q = 1) : d241234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26880, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26880, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26881 q = 1) (hb : d208034 q = 1) : d241235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26881, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26881, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26883 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64644 q ha hb
    | true =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64645 q ha hb
  have h12 (q : Pattern) (ha : d26884 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26885 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26886 q = 1) (hb : d208034 q = 1) : d241241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26886, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26886, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d26887 q = 1) (hb : d208034 q = 1) : d241242 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26887, d241242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26887, d241242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d26888 q = 1) (hb : d208034 q = 1) : d241243 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26888, d241243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26888, d241243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro64675 (p : Pattern) (ha : d26893 p = 1) (hb : d208034 p = 1) : d241248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26879 q = 1) (hb : d208034 q = 1) : d241233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26879, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64672 q ha hb
    | true =>
      simp only [d26879, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64644 q ha hb
  have h2 (q : Pattern) (ha : d26880 q = 1) (hb : d208034 q = 1) : d241234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26880, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26880, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26881 q = 1) (hb : d208034 q = 1) : d241235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26881, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26881, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26883 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64644 q ha hb
    | true =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64645 q ha hb
  have h5 (q : Pattern) (ha : d26884 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26885 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26886 q = 1) (hb : d208034 q = 1) : d241241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26886, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26886, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26891 q = 1) (hb : d208034 q = 1) : d241246 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26891, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26891, d241246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26892 q = 1) (hb : d208034 q = 1) : d241247 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26892, d241247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26892, d241247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26893 q = 1) (hb : d208034 q = 1) : d241248 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26893, d241248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26893, d241248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64676 (p : Pattern) (ha : d26899 p = 1) (hb : d208034 p = 1) : d241254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26889 q = 1) (hb : d208034 q = 1) : d241244 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26889, d241244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64674 q ha hb
    | true =>
      simp only [d26889, d241244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26890 q = 1) (hb : d208034 q = 1) : d241245 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26890, d241245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26890, d241245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26894 q = 1) (hb : d208034 q = 1) : d241249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26894, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64675 q ha hb
    | true =>
      simp only [d26894, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26895 q = 1) (hb : d208034 q = 1) : d241250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26895, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26895, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26896 q = 1) (hb : d208034 q = 1) : d241251 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26896, d241251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26896, d241251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26897 q = 1) (hb : d208034 q = 1) : d241252 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26897, d241252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26897, d241252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26898 q = 1) (hb : d208034 q = 1) : d241253 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26898, d241253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26898, d241253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26899 q = 1) (hb : d208034 q = 1) : d241254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26899, d241254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26899, d241254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64677 (p : Pattern) (ha : d26907 p = 1) (hb : d208034 p = 1) : d241262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26894 q = 1) (hb : d208034 q = 1) : d241249 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26894, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64675 q ha hb
    | true =>
      simp only [d26894, d241249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26895 q = 1) (hb : d208034 q = 1) : d241250 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26895, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26895, d241250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26902 q = 1) (hb : d208034 q = 1) : d241257 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26902, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64646 q ha hb
    | true =>
      simp only [d26902, d241257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26903 q = 1) (hb : d208034 q = 1) : d241258 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26903, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26903, d241258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26904 q = 1) (hb : d208034 q = 1) : d241259 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26904, d241259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26904, d241259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26905 q = 1) (hb : d208034 q = 1) : d241260 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26905, d241260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26905, d241260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26906 q = 1) (hb : d208034 q = 1) : d241261 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26906, d241261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26906, d241261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26907 q = 1) (hb : d208034 q = 1) : d241262 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26907, d241262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26907, d241262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64678 (p : Pattern) (ha : d26967 p = 1) (hb : d208034 p = 1) : d241270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26873 q = 1) (hb : d208034 q = 1) : d26847 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26873, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26873, d26847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64629 q ha hb
  have h2 (q : Pattern) (ha : d26584 q = 1) (hb : d208034 q = 1) : d26568 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64629 q ha hb
    | true =>
      simp only [d26584, d26568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26874 q = 1) (hb : d208034 q = 1) : d26848 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26874, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26874, d26848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26585 q = 1) (hb : d208034 q = 1) : d26569 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26585, d26569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26875 q = 1) (hb : d208034 q = 1) : d26849 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26875, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26875, d26849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26876 q = 1) (hb : d208034 q = 1) : d26850 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26876, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26876, d26850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26858 q = 1) (hb : d208034 q = 1) : d241222 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26858, d241222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
  have h8 (q : Pattern) (ha : d26575 q = 1) (hb : d208034 q = 1) : d241061 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64627 q ha hb
    | true =>
      simp only [d26575, d241061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d26859 q = 1) (hb : d208034 q = 1) : d241223 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26859, d241223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26576 q = 1) (hb : d208034 q = 1) : d241062 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26576, d241062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d26860 q = 1) (hb : d208034 q = 1) : d241224 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d26860, d241224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26861 q = 1) (hb : d208034 q = 1) : d241225 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26861, d241225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d26877 q = 1) (hb : d208034 q = 1) : d241226 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26877, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26877, d241226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d26962 q = 1) (hb : d208034 q = 1) : d241265 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26962, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26962, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64657 q ha hb
  have h15 (q : Pattern) (ha : d26758 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64657 q ha hb
    | true =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d26963 q = 1) (hb : d208034 q = 1) : d241266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26963, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d26963, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d26759 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d26964 q = 1) (hb : d208034 q = 1) : d241267 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26964, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d26964, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d26965 q = 1) (hb : d208034 q = 1) : d241268 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26965, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d26965, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d26966 q = 1) (hb : d208034 q = 1) : d241269 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26966, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d26966, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d26967 q = 1) (hb : d208034 q = 1) : d241270 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26967, d241270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d26967, d241270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro64679 (p : Pattern) (ha : d26968 p = 1) (hb : d208034 p = 1) : d241271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26962 q = 1) (hb : d208034 q = 1) : d241265 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26962, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26962, d241265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64657 q ha hb
  have h2 (q : Pattern) (ha : d26758 q = 1) (hb : d208034 q = 1) : d241147 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64657 q ha hb
    | true =>
      simp only [d26758, d241147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26963 q = 1) (hb : d208034 q = 1) : d241266 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26963, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26963, d241266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26759 q = 1) (hb : d208034 q = 1) : d241148 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26759, d241148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26964 q = 1) (hb : d208034 q = 1) : d241267 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d26964, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26964, d241267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26965 q = 1) (hb : d208034 q = 1) : d241268 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d26965, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26965, d241268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d26966 q = 1) (hb : d208034 q = 1) : d241269 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d26966, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26966, d241269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d26968 q = 1) (hb : d208034 q = 1) : d241271 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d26968, d241271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26968, d241271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64680 (p : Pattern) (ha : d26974 p = 1) (hb : d208034 p = 1) : d241277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26879 q = 1) (hb : d208034 q = 1) : d241233 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26879, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64672 q ha hb
    | true =>
      simp only [d26879, d241233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64644 q ha hb
  have h2 (q : Pattern) (ha : d26880 q = 1) (hb : d208034 q = 1) : d241234 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26880, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26880, d241234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26881 q = 1) (hb : d208034 q = 1) : d241235 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26881, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26881, d241235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d26883 q = 1) (hb : d208034 q = 1) : d241238 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64644 q ha hb
    | true =>
      simp only [d26883, d241238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64645 q ha hb
  have h5 (q : Pattern) (ha : d26884 q = 1) (hb : d208034 q = 1) : d241239 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26884, d241239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d26885 q = 1) (hb : d208034 q = 1) : d241240 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26885, d241240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d26886 q = 1) (hb : d208034 q = 1) : d241241 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26886, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26886, d241241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d26969 q = 1) (hb : d208034 q = 1) : d241272 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d26969, d241272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64678 q ha hb
    | true =>
      simp only [d26969, d241272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64679 q ha hb
  have h9 (q : Pattern) (ha : d26970 q = 1) (hb : d208034 q = 1) : d241273 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d26970, d241273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26970, d241273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26971 q = 1) (hb : d208034 q = 1) : d241274 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d26971, d241274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26971, d241274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26972 q = 1) (hb : d208034 q = 1) : d241275 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d26972, d241275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26972, d241275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d26973 q = 1) (hb : d208034 q = 1) : d241276 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d26973, d241276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26973, d241276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d26974 q = 1) (hb : d208034 q = 1) : d241277 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d26974, d241277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d26974, d241277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro64681 (p : Pattern) (ha : d26980 p = 1) (hb : d208034 p = 1) : d241283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26975 q = 1) (hb : d208034 q = 1) : d241278 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d26975, d241278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64680 q ha hb
    | true =>
      simp only [d26975, d241278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d26976 q = 1) (hb : d208034 q = 1) : d241279 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d26976, d241279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26976, d241279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d26977 q = 1) (hb : d208034 q = 1) : d241280 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d26977, d241280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26977, d241280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26978 q = 1) (hb : d208034 q = 1) : d241281 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d26978, d241281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26978, d241281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26979 q = 1) (hb : d208034 q = 1) : d241282 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d26979, d241282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26979, d241282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d26980 q = 1) (hb : d208034 q = 1) : d241283 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d26980, d241283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26980, d241283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64682 (p : Pattern) (ha : d202199 p = 1) (hb : d208034 p = 1) : d241289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26908 q = 1) (hb : d208034 q = 1) : d241263 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26908, d241263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64676 q ha hb
    | true =>
      simp only [d26908, d241263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64677 q ha hb
  have h2 (q : Pattern) (ha : d202195 q = 1) (hb : d208034 q = 1) : d241264 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202195, d241264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202195, d241264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26981 q = 1) (hb : d208034 q = 1) : d241284 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d26981, d241284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64681 q ha hb
    | true =>
      simp only [d26981, d241284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d26982 q = 1) (hb : d208034 q = 1) : d241285 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d26982, d241285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26982, d241285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202196 q = 1) (hb : d208034 q = 1) : d241286 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202196, d241286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202196, d241286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202197 q = 1) (hb : d208034 q = 1) : d241287 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202197, d241287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202197, d241287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202198 q = 1) (hb : d208034 q = 1) : d241288 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202198, d241288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202198, d241288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202199 q = 1) (hb : d208034 q = 1) : d241289 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202199, d241289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202199, d241289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64683 (p : Pattern) (ha : d202205 p = 1) (hb : d208034 p = 1) : d241306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d26622 q = 1) (hb : d208034 q = 1) : d241100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26622, d241100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26622, d241100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64637 q ha hb
  have h2 (q : Pattern) (ha : d26623 q = 1) (hb : d208034 q = 1) : d241101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26623, d241101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d26623, d241101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d26632 q = 1) (hb : d208034 q = 1) : d241110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26632, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64637 q ha hb
    | true =>
      simp only [d26632, d241110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64640 q ha hb
  have h4 (q : Pattern) (ha : d26633 q = 1) (hb : d208034 q = 1) : d241111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d26633, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d26633, d241111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d26634 q = 1) (hb : d208034 q = 1) : d241112 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d26634, d241112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d26634, d241112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202183 q = 1) (hb : d208034 q = 1) : d241193 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202183, d241193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64662 q ha hb
    | true =>
      simp only [d202183, d241193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64669 q ha hb
  have h7 (q : Pattern) (ha : d26820 q = 1) (hb : d208034 q = 1) : d241206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26820, d241206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64641 q ha hb
    | true =>
      simp only [d26820, d241206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64642 q ha hb
  have h8 (q : Pattern) (ha : d202184 q = 1) (hb : d208034 q = 1) : d241207 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202184, d241207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202184, d241207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202185 q = 1) (hb : d208034 q = 1) : d241208 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202185, d241208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202185, d241208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202186 q = 1) (hb : d208034 q = 1) : d241209 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202186, d241209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202186, d241209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202190 q = 1) (hb : d208034 q = 1) : d241213 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202190, d241213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202190, d241213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64670 q ha hb
  have h12 (q : Pattern) (ha : d26829 q = 1) (hb : d208034 q = 1) : d241215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26829, d241215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26829, d241215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64643 q ha hb
  have h13 (q : Pattern) (ha : d202191 q = 1) (hb : d208034 q = 1) : d241216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202191, d241216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202191, d241216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202192 q = 1) (hb : d208034 q = 1) : d241217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202192, d241217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202192, d241217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202193 q = 1) (hb : d208034 q = 1) : d241218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202193, d241218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202193, d241218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202194 q = 1) (hb : d208034 q = 1) : d241219 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202194, d241219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202194, d241219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202200 q = 1) (hb : d208034 q = 1) : d241290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202200, d241290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202200, d241290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64682 q ha hb
  have h18 (q : Pattern) (ha : d26998 q = 1) (hb : d208034 q = 1) : d241301 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d26998, d241301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d26998, d241301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64648 q ha hb
  have h19 (q : Pattern) (ha : d202201 q = 1) (hb : d208034 q = 1) : d241302 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202201, d241302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202201, d241302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202202 q = 1) (hb : d208034 q = 1) : d241303 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202202, d241303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202202, d241303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202203 q = 1) (hb : d208034 q = 1) : d241304 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202203, d241304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202203, d241304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202204 q = 1) (hb : d208034 q = 1) : d241305 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202204, d241305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202204, d241305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202205 q = 1) (hb : d208034 q = 1) : d241306 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202205, d241306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202205, d241306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro64684 (p : Pattern) (ha : d202211 p = 1) (hb : d208034 p = 1) : d241312 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202206 q = 1) (hb : d208034 q = 1) : d241307 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202206, d241307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202206, d241307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64683 q ha hb
  have h2 (q : Pattern) (ha : d202207 q = 1) (hb : d208034 q = 1) : d241308 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202207, d241308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202207, d241308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202208 q = 1) (hb : d208034 q = 1) : d241309 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202208, d241309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202208, d241309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202209 q = 1) (hb : d208034 q = 1) : d241310 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202209, d241310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202209, d241310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202210 q = 1) (hb : d208034 q = 1) : d241311 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202210, d241311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202210, d241311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202211 q = 1) (hb : d208034 q = 1) : d241312 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202211, d241312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202211, d241312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64685 (p : Pattern) (ha : d27025 p = 1) (hb : d208034 p = 1) : d241317 p = 1 := by
  have h0 (q : Pattern) (ha : d5717 q = 1) (hb : d208034 q = 1) : d5717 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2076 q = 1) (hb : d152852 q = 1) : d2076 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10408 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10409 q = 1) (hb : d208034 q = 1) : d2077 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, d208034, d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10409, d208034, d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10410 q = 1) (hb : d208034 q = 1) : d2078 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, d2078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10410, d2078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27025 q = 1) (hb : d208034 q = 1) : d241317 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27025, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27025, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64686 (p : Pattern) (ha : d27031 p = 1) (hb : d208034 p = 1) : d241323 p = 1 := by
  have h0 (q : Pattern) (ha : d27024 q = 1) (hb : d208034 q = 1) : d27024 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27023 q = 1) (hb : d208034 q = 1) : d27023 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d27026 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
    | true =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27027 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d27028 q = 1) (hb : d208034 q = 1) : d241320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27028, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27028, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27029 q = 1) (hb : d208034 q = 1) : d241321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27029, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27029, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d27030 q = 1) (hb : d208034 q = 1) : d241322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27030, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27030, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27031 q = 1) (hb : d208034 q = 1) : d241323 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27031, d241323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27031, d241323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64687 (p : Pattern) (ha : d27035 p = 1) (hb : d208034 p = 1) : d241317 p = 1 := by
  have h0 (q : Pattern) (ha : d5715 q = 1) (hb : d152852 q = 1) : d5715 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27032 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27033 q = 1) (hb : d208034 q = 1) : d5716 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27033, d208034, d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27033, d208034, d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d27034 q = 1) (hb : d208034 q = 1) : d5717 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27034, d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27034, d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2076 q = 1) (hb : d152852 q = 1) : d2076 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10408 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d10409 q = 1) (hb : d208034 q = 1) : d2077 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, d208034, d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10409, d208034, d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d10410 q = 1) (hb : d208034 q = 1) : d2078 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, d2078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10410, d2078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d27035 q = 1) (hb : d208034 q = 1) : d241317 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27035, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27035, d241317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64688 (p : Pattern) (ha : d27042 p = 1) (hb : d208034 p = 1) : d241325 p = 1 := by
  have h0 (q : Pattern) (ha : d27023 q = 1) (hb : d208034 q = 1) : d27023 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27036 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
    | true =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27037 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27038 q = 1) (hb : d208034 q = 1) : d241320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27038, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27038, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27039 q = 1) (hb : d208034 q = 1) : d241321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27039, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27039, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27040 q = 1) (hb : d208034 q = 1) : d241322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27040, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27040, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27026 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
    | true =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27027 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d27028 q = 1) (hb : d208034 q = 1) : d241320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27028, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27028, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27029 q = 1) (hb : d208034 q = 1) : d241321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27029, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27029, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d27041 q = 1) (hb : d208034 q = 1) : d241324 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27041, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27041, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d27042 q = 1) (hb : d208034 q = 1) : d241325 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27042, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27042, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro64689 (p : Pattern) (ha : d10411 p = 1) (hb : d208034 p = 1) : d2079 p = 1 := by
  have h0 (q : Pattern) (ha : d2076 q = 1) (hb : d152852 q = 1) : d2076 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10408 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10409 q = 1) (hb : d208034 q = 1) : d2077 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10409, d208034, d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10409, d208034, d2077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10410 q = 1) (hb : d208034 q = 1) : d2078 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10410, d2078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10410, d2078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10411 q = 1) (hb : d208034 q = 1) : d2079 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10411, d2079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10411, d2079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro64690 (p : Pattern) (ha : d27047 p = 1) (hb : d208034 p = 1) : d241329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27036 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
    | true =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27037 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27038 q = 1) (hb : d208034 q = 1) : d241320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27038, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27038, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27039 q = 1) (hb : d208034 q = 1) : d241321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27039, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27039, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27046 q = 1) (hb : d208034 q = 1) : d241324 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27046, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27046, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d208034 q = 1) : d2080 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d2080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64689 q ha hb
    | true =>
      simp only [d10412, d2080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d208034 q = 1) : d2081 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d2081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d2081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d208034 q = 1) : d2082 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d2082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d2082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d208034 q = 1) : d2083 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d2083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d2083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d208034 q = 1) : d2084 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d2084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d2084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27047 q = 1) (hb : d208034 q = 1) : d241329 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27047, d241329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27047, d241329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64691 (p : Pattern) (ha : d27054 p = 1) (hb : d208034 p = 1) : d241336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27043 q = 1) (hb : d208034 q = 1) : d241326 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27043, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64686 q ha hb
    | true =>
      simp only [d27043, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64688 q ha hb
  have h2 (q : Pattern) (ha : d27044 q = 1) (hb : d208034 q = 1) : d241327 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27044, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27044, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27045 q = 1) (hb : d208034 q = 1) : d241328 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27045, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27045, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27048 q = 1) (hb : d208034 q = 1) : d241330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64688 q ha hb
    | true =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64690 q ha hb
  have h5 (q : Pattern) (ha : d27049 q = 1) (hb : d208034 q = 1) : d241331 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27050 q = 1) (hb : d208034 q = 1) : d241332 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27051 q = 1) (hb : d208034 q = 1) : d241333 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27051, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27051, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27052 q = 1) (hb : d208034 q = 1) : d241334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27052, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27052, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27053 q = 1) (hb : d208034 q = 1) : d241335 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27053, d241335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27053, d241335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27054 q = 1) (hb : d208034 q = 1) : d241336 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27054, d241336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27054, d241336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64692 (p : Pattern) (ha : d27058 p = 1) (hb : d208034 p = 1) : d241340 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27048 q = 1) (hb : d208034 q = 1) : d241330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64688 q ha hb
    | true =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64690 q ha hb
  have h2 (q : Pattern) (ha : d27049 q = 1) (hb : d208034 q = 1) : d241331 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27050 q = 1) (hb : d208034 q = 1) : d241332 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27052 q = 1) (hb : d208034 q = 1) : d241334 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27052, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27052, d241334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27057 q = 1) (hb : d208034 q = 1) : d241339 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27057, d241339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27057, d241339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27058 q = 1) (hb : d208034 q = 1) : d241340 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27058, d241340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27058, d241340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64693 (p : Pattern) (ha : d27064 p = 1) (hb : d208034 p = 1) : d241346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d208034 q = 1) : d241343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d208034 q = 1) : d241344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27063 q = 1) (hb : d208034 q = 1) : d241345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27063, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27063, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27064 q = 1) (hb : d208034 q = 1) : d241346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27064, d241346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27064, d241346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64694 (p : Pattern) (ha : d27068 p = 1) (hb : d208034 p = 1) : d241350 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d208034 q = 1) : d241347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d208034 q = 1) : d241348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27067 q = 1) (hb : d208034 q = 1) : d241349 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27067, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27067, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27068 q = 1) (hb : d208034 q = 1) : d241350 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27068, d241350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27068, d241350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64695 (p : Pattern) (ha : d27074 p = 1) (hb : d208034 p = 1) : d241356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27069 q = 1) (hb : d208034 q = 1) : d241351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27069, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64693 q ha hb
    | true =>
      simp only [d27069, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64694 q ha hb
  have h2 (q : Pattern) (ha : d27070 q = 1) (hb : d208034 q = 1) : d241352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27070, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27070, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27071 q = 1) (hb : d208034 q = 1) : d241353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27071, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27071, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27072 q = 1) (hb : d208034 q = 1) : d241354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27072, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27072, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27073 q = 1) (hb : d208034 q = 1) : d241355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27073, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27073, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27074 q = 1) (hb : d208034 q = 1) : d241356 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27074, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27074, d241356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64696 (p : Pattern) (ha : d27077 p = 1) (hb : d208034 p = 1) : d241359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d208034 q = 1) : d241343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d208034 q = 1) : d241344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27063 q = 1) (hb : d208034 q = 1) : d241345 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27063, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27063, d241345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27077 q = 1) (hb : d208034 q = 1) : d241359 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27077, d241359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27077, d241359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64697 (p : Pattern) (ha : d27078 p = 1) (hb : d208034 p = 1) : d241360 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d208034 q = 1) : d241347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d208034 q = 1) : d241348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27067 q = 1) (hb : d208034 q = 1) : d241349 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27067, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27067, d241349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27078 q = 1) (hb : d208034 q = 1) : d241360 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27078, d241360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27078, d241360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64698 (p : Pattern) (ha : d27084 p = 1) (hb : d208034 p = 1) : d241366 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27069 q = 1) (hb : d208034 q = 1) : d241351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27069, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64693 q ha hb
    | true =>
      simp only [d27069, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64694 q ha hb
  have h2 (q : Pattern) (ha : d27070 q = 1) (hb : d208034 q = 1) : d241352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27070, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27070, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27071 q = 1) (hb : d208034 q = 1) : d241353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27071, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27071, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27072 q = 1) (hb : d208034 q = 1) : d241354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27072, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27072, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27073 q = 1) (hb : d208034 q = 1) : d241355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27073, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27073, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27079 q = 1) (hb : d208034 q = 1) : d241361 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27079, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64696 q ha hb
    | true =>
      simp only [d27079, d241361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64697 q ha hb
  have h7 (q : Pattern) (ha : d27080 q = 1) (hb : d208034 q = 1) : d241362 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27080, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27080, d241362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27081 q = 1) (hb : d208034 q = 1) : d241363 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27081, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27081, d241363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27082 q = 1) (hb : d208034 q = 1) : d241364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27082, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27082, d241364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27083 q = 1) (hb : d208034 q = 1) : d241365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27083, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27083, d241365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27084 q = 1) (hb : d208034 q = 1) : d241366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27084, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27084, d241366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64699 (p : Pattern) (ha : d27246 p = 1) (hb : d208034 p = 1) : d241454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27069 q = 1) (hb : d208034 q = 1) : d241351 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27069, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64693 q ha hb
    | true =>
      simp only [d27069, d241351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64694 q ha hb
  have h2 (q : Pattern) (ha : d27070 q = 1) (hb : d208034 q = 1) : d241352 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27070, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27070, d241352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27071 q = 1) (hb : d208034 q = 1) : d241353 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27071, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27071, d241353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27072 q = 1) (hb : d208034 q = 1) : d241354 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27072, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27072, d241354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27073 q = 1) (hb : d208034 q = 1) : d241355 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27073, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27073, d241355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27241 q = 1) (hb : d208034 q = 1) : d241449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27241, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64694 q ha hb
    | true =>
      simp only [d27241, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27242 q = 1) (hb : d208034 q = 1) : d241450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27242, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27242, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27243 q = 1) (hb : d208034 q = 1) : d241451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27243, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27243, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27244 q = 1) (hb : d208034 q = 1) : d241452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27244, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27244, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27245 q = 1) (hb : d208034 q = 1) : d241453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27245, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27245, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27246 q = 1) (hb : d208034 q = 1) : d241454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27246, d241454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27246, d241454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64700 (p : Pattern) (ha : d27252 p = 1) (hb : d208034 p = 1) : d241460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27241 q = 1) (hb : d208034 q = 1) : d241449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27241, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64694 q ha hb
    | true =>
      simp only [d27241, d241449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27242 q = 1) (hb : d208034 q = 1) : d241450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27242, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27242, d241450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27243 q = 1) (hb : d208034 q = 1) : d241451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27243, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27243, d241451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27244 q = 1) (hb : d208034 q = 1) : d241452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27244, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27244, d241452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27245 q = 1) (hb : d208034 q = 1) : d241453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27245, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27245, d241453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27247 q = 1) (hb : d208034 q = 1) : d241455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27247, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64697 q ha hb
    | true =>
      simp only [d27247, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27248 q = 1) (hb : d208034 q = 1) : d241456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27248, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27248, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27249 q = 1) (hb : d208034 q = 1) : d241457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27249, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27249, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27250 q = 1) (hb : d208034 q = 1) : d241458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27250, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27250, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27251 q = 1) (hb : d208034 q = 1) : d241459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27251, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27251, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27252 q = 1) (hb : d208034 q = 1) : d241460 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27252, d241460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27252, d241460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro64701 (p : Pattern) (ha : d27261 p = 1) (hb : d208034 p = 1) : d241469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27247 q = 1) (hb : d208034 q = 1) : d241455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27247, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64697 q ha hb
    | true =>
      simp only [d27247, d241455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27248 q = 1) (hb : d208034 q = 1) : d241456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27248, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27248, d241456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27249 q = 1) (hb : d208034 q = 1) : d241457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27249, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27249, d241457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27250 q = 1) (hb : d208034 q = 1) : d241458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27250, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27250, d241458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27251 q = 1) (hb : d208034 q = 1) : d241459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27251, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27251, d241459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27261 q = 1) (hb : d208034 q = 1) : d241469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27261, d241469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27261, d241469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64702 (p : Pattern) (ha : d27298 p = 1) (hb : d208034 p = 1) : d241485 p = 1 := by
  have h0 (q : Pattern) (ha : d27275 q = 1) (hb : d208034 q = 1) : d27275 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27293 q = 1) (hb : d208034 q = 1) : d241475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27293, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27293, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
  have h3 (q : Pattern) (ha : d27036 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
    | true =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27294 q = 1) (hb : d208034 q = 1) : d241476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27294, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27294, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27037 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27295 q = 1) (hb : d208034 q = 1) : d241477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27295, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27295, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27296 q = 1) (hb : d208034 q = 1) : d241478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27296, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27296, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27297 q = 1) (hb : d208034 q = 1) : d241479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27297, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27297, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27278 q = 1) (hb : d208034 q = 1) : d241475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27278, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27278, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
  have h10 (q : Pattern) (ha : d27026 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
    | true =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d27279 q = 1) (hb : d208034 q = 1) : d241476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27279, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27279, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27027 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d27280 q = 1) (hb : d208034 q = 1) : d241477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27280, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27280, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27281 q = 1) (hb : d208034 q = 1) : d241478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27281, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27281, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d27287 q = 1) (hb : d208034 q = 1) : d241484 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27287, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d27287, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d27298 q = 1) (hb : d208034 q = 1) : d241485 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27298, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27298, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro64703 (p : Pattern) (ha : d27303 p = 1) (hb : d208034 p = 1) : d241490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27293 q = 1) (hb : d208034 q = 1) : d241475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27293, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27293, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
  have h2 (q : Pattern) (ha : d27036 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
    | true =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27294 q = 1) (hb : d208034 q = 1) : d241476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27294, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27294, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27037 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27295 q = 1) (hb : d208034 q = 1) : d241477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27295, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27295, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27296 q = 1) (hb : d208034 q = 1) : d241478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27296, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27296, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27302 q = 1) (hb : d208034 q = 1) : d241484 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27302, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27302, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d208034 q = 1) : d2361 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d2361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d2361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64689 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d208034 q = 1) : d2080 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d2080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64689 q ha hb
    | true =>
      simp only [d10412, d2080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d208034 q = 1) : d2362 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d2362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d2362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d208034 q = 1) : d2081 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d2081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d2081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d208034 q = 1) : d2363 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d2363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d2363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d208034 q = 1) : d2364 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d2364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d2364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d208034 q = 1) : d2365 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d2365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d2365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d27303 q = 1) (hb : d208034 q = 1) : d241490 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27303, d241490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27303, d241490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64704 (p : Pattern) (ha : d27322 p = 1) (hb : d208034 p = 1) : d241509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27304 q = 1) (hb : d208034 q = 1) : d241491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64702 q ha hb
    | true =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64703 q ha hb
  have h2 (q : Pattern) (ha : d27305 q = 1) (hb : d208034 q = 1) : d241492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27306 q = 1) (hb : d208034 q = 1) : d241493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27312 q = 1) (hb : d208034 q = 1) : d241499 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27312, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27312, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27321 q = 1) (hb : d208034 q = 1) : d241508 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27321, d241508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27321, d241508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27322 q = 1) (hb : d208034 q = 1) : d241509 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27322, d241509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27322, d241509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64705 (p : Pattern) (ha : d27414 p = 1) (hb : d208034 p = 1) : d241547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27323 q = 1) (hb : d208034 q = 1) : d241510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27323, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64704 q ha hb
    | true =>
      simp only [d27323, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27324 q = 1) (hb : d208034 q = 1) : d241511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27324, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27324, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27411 q = 1) (hb : d208034 q = 1) : d241544 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27411, d241544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27411, d241544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27412 q = 1) (hb : d208034 q = 1) : d241545 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27412, d241545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27412, d241545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27413 q = 1) (hb : d208034 q = 1) : d241546 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27413, d241546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27413, d241546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27414 q = 1) (hb : d208034 q = 1) : d241547 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27414, d241547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27414, d241547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64706 (p : Pattern) (ha : d27420 p = 1) (hb : d208034 p = 1) : d241553 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27415 q = 1) (hb : d208034 q = 1) : d241548 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27415, d241548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64705 q ha hb
    | true =>
      simp only [d27415, d241548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27416 q = 1) (hb : d208034 q = 1) : d241549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27416, d241549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27416, d241549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27417 q = 1) (hb : d208034 q = 1) : d241550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27417, d241550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27417, d241550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27418 q = 1) (hb : d208034 q = 1) : d241551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27418, d241551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27418, d241551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27419 q = 1) (hb : d208034 q = 1) : d241552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d27419, d241552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27419, d241552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27420 q = 1) (hb : d208034 q = 1) : d241553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d27420, d241553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27420, d241553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64707 (p : Pattern) (ha : d27089 p = 1) (hb : d208034 p = 1) : d241371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d208034 q = 1) : d241343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d208034 q = 1) : d241344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27088 q = 1) (hb : d208034 q = 1) : d241370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27088, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27088, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27089 q = 1) (hb : d208034 q = 1) : d241371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27089, d241371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27089, d241371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64708 (p : Pattern) (ha : d27091 p = 1) (hb : d208034 p = 1) : d241373 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d208034 q = 1) : d241347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d208034 q = 1) : d241348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27090 q = 1) (hb : d208034 q = 1) : d241372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27090, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27090, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27091 q = 1) (hb : d208034 q = 1) : d241373 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27091, d241373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27091, d241373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64709 (p : Pattern) (ha : d27098 p = 1) (hb : d208034 p = 1) : d241380 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d208034 q = 1) : d241343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27096 q = 1) (hb : d208034 q = 1) : d241378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27096, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27096, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27097 q = 1) (hb : d208034 q = 1) : d241379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27097, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27097, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27098 q = 1) (hb : d208034 q = 1) : d241380 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27098, d241380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27098, d241380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64710 (p : Pattern) (ha : d27101 p = 1) (hb : d208034 p = 1) : d241383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d208034 q = 1) : d241347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27099 q = 1) (hb : d208034 q = 1) : d241381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27099, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27099, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27100 q = 1) (hb : d208034 q = 1) : d241382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27100, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27100, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27101 q = 1) (hb : d208034 q = 1) : d241383 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27101, d241383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27101, d241383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64711 (p : Pattern) (ha : d27110 p = 1) (hb : d208034 p = 1) : d241325 p = 1 := by
  have h0 (q : Pattern) (ha : d27023 q = 1) (hb : d208034 q = 1) : d27023 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27026 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
    | true =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27027 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27028 q = 1) (hb : d208034 q = 1) : d241320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27028, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27028, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27029 q = 1) (hb : d208034 q = 1) : d241321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27029, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27029, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27030 q = 1) (hb : d208034 q = 1) : d241322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27030, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27030, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27041 q = 1) (hb : d208034 q = 1) : d241324 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27041, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27041, d241324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27110 q = 1) (hb : d208034 q = 1) : d241325 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27110, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27110, d241325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64712 (p : Pattern) (ha : d27116 p = 1) (hb : d208034 p = 1) : d241392 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27106 q = 1) (hb : d208034 q = 1) : d27106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27107 q = 1) (hb : d208034 q = 1) : d241387 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27107, d241387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27107, d241387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64686 q ha hb
  have h3 (q : Pattern) (ha : d27108 q = 1) (hb : d208034 q = 1) : d241388 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27108, d241388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27108, d241388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27109 q = 1) (hb : d208034 q = 1) : d241389 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27109, d241389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27109, d241389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27111 q = 1) (hb : d208034 q = 1) : d241326 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27111, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64686 q ha hb
    | true =>
      simp only [d27111, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64711 q ha hb
  have h6 (q : Pattern) (ha : d27112 q = 1) (hb : d208034 q = 1) : d241327 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27112, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27112, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27113 q = 1) (hb : d208034 q = 1) : d241328 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27113, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27113, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27114 q = 1) (hb : d208034 q = 1) : d241390 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27114, d241390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27114, d241390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27043 q = 1) (hb : d208034 q = 1) : d241326 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27043, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64686 q ha hb
    | true =>
      simp only [d27043, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64688 q ha hb
  have h10 (q : Pattern) (ha : d27044 q = 1) (hb : d208034 q = 1) : d241327 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27044, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27044, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27045 q = 1) (hb : d208034 q = 1) : d241328 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27045, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27045, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27048 q = 1) (hb : d208034 q = 1) : d241330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64688 q ha hb
    | true =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64690 q ha hb
  have h13 (q : Pattern) (ha : d27049 q = 1) (hb : d208034 q = 1) : d241331 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27050 q = 1) (hb : d208034 q = 1) : d241332 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27051 q = 1) (hb : d208034 q = 1) : d241333 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27051, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27051, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27115 q = 1) (hb : d208034 q = 1) : d241391 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27115, d241391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27115, d241391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27116 q = 1) (hb : d208034 q = 1) : d241392 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27116, d241392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d27116, d241392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro64713 (p : Pattern) (ha : d27122 p = 1) (hb : d208034 p = 1) : d241398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27117 q = 1) (hb : d208034 q = 1) : d241393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27117, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64712 q ha hb
    | true =>
      simp only [d27117, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27118 q = 1) (hb : d208034 q = 1) : d241394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27118, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27118, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27119 q = 1) (hb : d208034 q = 1) : d241395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27119, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27119, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27120 q = 1) (hb : d208034 q = 1) : d241396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27120, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27120, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27121 q = 1) (hb : d208034 q = 1) : d241397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27121, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27121, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27122 q = 1) (hb : d208034 q = 1) : d241398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27122, d241398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27122, d241398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64714 (p : Pattern) (ha : d27184 p = 1) (hb : d208034 p = 1) : d241401 p = 1 := by
  have h0 (q : Pattern) (ha : d5717 q = 1) (hb : d208034 q = 1) : d5717 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27181 q = 1) (hb : d152852 q = 1) : d27181 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2061 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d27182 q = 1) (hb : d208034 q = 1) : d239849 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27182, d208034, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27182, d208034, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d27183 q = 1) (hb : d208034 q = 1) : d239850 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27183, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27183, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27184 q = 1) (hb : d208034 q = 1) : d241401 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27184, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27184, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64715 (p : Pattern) (ha : d27190 p = 1) (hb : d208034 p = 1) : d241407 p = 1 := by
  have h0 (q : Pattern) (ha : d27023 q = 1) (hb : d208034 q = 1) : d27023 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27036 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
    | true =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27037 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27038 q = 1) (hb : d208034 q = 1) : d241320 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27038, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27038, d241320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27039 q = 1) (hb : d208034 q = 1) : d241321 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27039, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27039, d241321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27040 q = 1) (hb : d208034 q = 1) : d241322 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27040, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27040, d241322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27185 q = 1) (hb : d208034 q = 1) : d241402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27185, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64714 q ha hb
    | true =>
      simp only [d27185, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27186 q = 1) (hb : d208034 q = 1) : d241403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27186, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27186, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h9 (q : Pattern) (ha : d27187 q = 1) (hb : d208034 q = 1) : d241404 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27187, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27187, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27188 q = 1) (hb : d208034 q = 1) : d241405 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27188, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27188, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d27189 q = 1) (hb : d208034 q = 1) : d241406 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27189, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27189, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d27190 q = 1) (hb : d208034 q = 1) : d241407 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27190, d241407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27190, d241407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro64716 (p : Pattern) (ha : d27191 p = 1) (hb : d208034 p = 1) : d241401 p = 1 := by
  have h0 (q : Pattern) (ha : d5715 q = 1) (hb : d152852 q = 1) : d5715 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d27032 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27033 q = 1) (hb : d208034 q = 1) : d5716 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27033, d208034, d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27033, d208034, d5716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d27034 q = 1) (hb : d208034 q = 1) : d5717 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27034, d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27034, d5717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27181 q = 1) (hb : d152852 q = 1) : d27181 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2061 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d27182 q = 1) (hb : d208034 q = 1) : d239849 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27182, d208034, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27182, d208034, d239849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d27183 q = 1) (hb : d208034 q = 1) : d239850 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27183, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27183, d239850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d27191 q = 1) (hb : d208034 q = 1) : d241401 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27191, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27191, d241401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro64717 (p : Pattern) (ha : d27197 p = 1) (hb : d208034 p = 1) : d241408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27192 q = 1) (hb : d208034 q = 1) : d241402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27192, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64716 q ha hb
    | true =>
      simp only [d27192, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27193 q = 1) (hb : d208034 q = 1) : d241403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27193, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27193, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27194 q = 1) (hb : d208034 q = 1) : d241404 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27194, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27194, d241404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27195 q = 1) (hb : d208034 q = 1) : d241405 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27195, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27195, d241405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27196 q = 1) (hb : d208034 q = 1) : d241406 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27196, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27196, d241406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27197 q = 1) (hb : d208034 q = 1) : d241408 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27197, d241408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27197, d241408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64718 (p : Pattern) (ha : d27203 p = 1) (hb : d208034 p = 1) : d241414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27043 q = 1) (hb : d208034 q = 1) : d241326 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27043, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64686 q ha hb
    | true =>
      simp only [d27043, d241326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64688 q ha hb
  have h2 (q : Pattern) (ha : d27044 q = 1) (hb : d208034 q = 1) : d241327 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27044, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27044, d241327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27045 q = 1) (hb : d208034 q = 1) : d241328 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27045, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27045, d241328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27048 q = 1) (hb : d208034 q = 1) : d241330 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64688 q ha hb
    | true =>
      simp only [d27048, d241330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64690 q ha hb
  have h5 (q : Pattern) (ha : d27049 q = 1) (hb : d208034 q = 1) : d241331 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27049, d241331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27050 q = 1) (hb : d208034 q = 1) : d241332 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27050, d241332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27051 q = 1) (hb : d208034 q = 1) : d241333 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27051, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27051, d241333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27198 q = 1) (hb : d208034 q = 1) : d241409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27198, d241409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64715 q ha hb
    | true =>
      simp only [d27198, d241409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64717 q ha hb
  have h9 (q : Pattern) (ha : d27199 q = 1) (hb : d208034 q = 1) : d241410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27199, d241410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27199, d241410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27200 q = 1) (hb : d208034 q = 1) : d241411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27200, d241411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27200, d241411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27201 q = 1) (hb : d208034 q = 1) : d241412 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27201, d241412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27201, d241412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27202 q = 1) (hb : d208034 q = 1) : d241413 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27202, d241413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27202, d241413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27203 q = 1) (hb : d208034 q = 1) : d241414 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27203, d241414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27203, d241414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro64719 (p : Pattern) (ha : d27209 p = 1) (hb : d208034 p = 1) : d241420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27204 q = 1) (hb : d208034 q = 1) : d241415 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27204, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64718 q ha hb
    | true =>
      simp only [d27204, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27205 q = 1) (hb : d208034 q = 1) : d241416 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27205, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27205, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27206 q = 1) (hb : d208034 q = 1) : d241417 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27206, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27206, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27207 q = 1) (hb : d208034 q = 1) : d241418 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27207, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27207, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27208 q = 1) (hb : d208034 q = 1) : d241419 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27208, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27208, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27209 q = 1) (hb : d208034 q = 1) : d241420 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27209, d241420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27209, d241420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64720 (p : Pattern) (ha : d202220 p = 1) (hb : d208034 p = 1) : d241426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27092 q = 1) (hb : d208034 q = 1) : d241374 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27092, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64707 q ha hb
    | true =>
      simp only [d27092, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64708 q ha hb
  have h2 (q : Pattern) (ha : d27093 q = 1) (hb : d208034 q = 1) : d241375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27093, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27093, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27094 q = 1) (hb : d208034 q = 1) : d241376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27094, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27094, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27095 q = 1) (hb : d208034 q = 1) : d241377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27095, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27095, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27102 q = 1) (hb : d208034 q = 1) : d241384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27102, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64709 q ha hb
    | true =>
      simp only [d27102, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64710 q ha hb
  have h6 (q : Pattern) (ha : d27103 q = 1) (hb : d208034 q = 1) : d241385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27103, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27103, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27104 q = 1) (hb : d208034 q = 1) : d241386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27104, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27104, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27123 q = 1) (hb : d208034 q = 1) : d241399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27123, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64713 q ha hb
    | true =>
      simp only [d27123, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64693 q ha hb
  have h9 (q : Pattern) (ha : d202216 q = 1) (hb : d208034 q = 1) : d241400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202216, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d27210 q = 1) (hb : d208034 q = 1) : d241421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27210, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64719 q ha hb
    | true =>
      simp only [d27210, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27211 q = 1) (hb : d208034 q = 1) : d241422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27211, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27211, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202217 q = 1) (hb : d208034 q = 1) : d241423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202217, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202218 q = 1) (hb : d208034 q = 1) : d241424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202218, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202219 q = 1) (hb : d208034 q = 1) : d241425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202219, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202220 q = 1) (hb : d208034 q = 1) : d241426 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202220, d241426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202220, d241426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro64721 (p : Pattern) (ha : d27216 p = 1) (hb : d208034 p = 1) : d241427 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d208034 q = 1) : d241343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27062 q = 1) (hb : d208034 q = 1) : d241344 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27062, d241344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27088 q = 1) (hb : d208034 q = 1) : d241370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27088, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27088, d241370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27216 q = 1) (hb : d208034 q = 1) : d241427 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27216, d241427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27216, d241427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64722 (p : Pattern) (ha : d27217 p = 1) (hb : d208034 p = 1) : d241428 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d208034 q = 1) : d241347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27066 q = 1) (hb : d208034 q = 1) : d241348 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27066, d241348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27090 q = 1) (hb : d208034 q = 1) : d241372 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27090, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27090, d241372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27217 q = 1) (hb : d208034 q = 1) : d241428 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27217, d241428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27217, d241428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64723 (p : Pattern) (ha : d27222 p = 1) (hb : d208034 p = 1) : d241433 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27061 q = 1) (hb : d208034 q = 1) : d241343 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27061, d241343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27096 q = 1) (hb : d208034 q = 1) : d241378 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27096, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27096, d241378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27097 q = 1) (hb : d208034 q = 1) : d241379 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27097, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27097, d241379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27222 q = 1) (hb : d208034 q = 1) : d241433 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27222, d241433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27222, d241433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64724 (p : Pattern) (ha : d27223 p = 1) (hb : d208034 p = 1) : d241434 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27059 q = 1) (hb : d208034 q = 1) : d241341 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64692 q ha hb
    | true =>
      simp only [d27059, d241341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27060 q = 1) (hb : d208034 q = 1) : d241342 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27060, d241342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27065 q = 1) (hb : d208034 q = 1) : d241347 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27065, d241347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27099 q = 1) (hb : d208034 q = 1) : d241381 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27099, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27099, d241381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27100 q = 1) (hb : d208034 q = 1) : d241382 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27100, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27100, d241382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27223 q = 1) (hb : d208034 q = 1) : d241434 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27223, d241434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27223, d241434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64725 (p : Pattern) (ha : d27227 p = 1) (hb : d208034 p = 1) : d241438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27117 q = 1) (hb : d208034 q = 1) : d241393 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27117, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64712 q ha hb
    | true =>
      simp only [d27117, d241393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27118 q = 1) (hb : d208034 q = 1) : d241394 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27118, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27118, d241394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27055 q = 1) (hb : d208034 q = 1) : d241337 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64691 q ha hb
    | true =>
      simp only [d27055, d241337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27056 q = 1) (hb : d208034 q = 1) : d241338 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27056, d241338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27119 q = 1) (hb : d208034 q = 1) : d241395 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27119, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27119, d241395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27120 q = 1) (hb : d208034 q = 1) : d241396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27120, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27120, d241396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27121 q = 1) (hb : d208034 q = 1) : d241397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27121, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27121, d241397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27227 q = 1) (hb : d208034 q = 1) : d241438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27227, d241438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27227, d241438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64726 (p : Pattern) (ha : d27233 p = 1) (hb : d208034 p = 1) : d241441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27204 q = 1) (hb : d208034 q = 1) : d241415 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27204, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64718 q ha hb
    | true =>
      simp only [d27204, d241415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27205 q = 1) (hb : d208034 q = 1) : d241416 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27205, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27205, d241416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27206 q = 1) (hb : d208034 q = 1) : d241417 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27206, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27206, d241417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27207 q = 1) (hb : d208034 q = 1) : d241418 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27207, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27207, d241418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27208 q = 1) (hb : d208034 q = 1) : d241419 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27208, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27208, d241419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27233 q = 1) (hb : d208034 q = 1) : d241441 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27233, d241441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27233, d241441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64727 (p : Pattern) (ha : d202225 p = 1) (hb : d208034 p = 1) : d241447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27092 q = 1) (hb : d208034 q = 1) : d241374 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27092, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64707 q ha hb
    | true =>
      simp only [d27092, d241374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64708 q ha hb
  have h2 (q : Pattern) (ha : d27093 q = 1) (hb : d208034 q = 1) : d241375 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27093, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27093, d241375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27094 q = 1) (hb : d208034 q = 1) : d241376 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27094, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27094, d241376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27095 q = 1) (hb : d208034 q = 1) : d241377 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27095, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27095, d241377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27102 q = 1) (hb : d208034 q = 1) : d241384 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27102, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64709 q ha hb
    | true =>
      simp only [d27102, d241384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64710 q ha hb
  have h6 (q : Pattern) (ha : d27103 q = 1) (hb : d208034 q = 1) : d241385 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27103, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27103, d241385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27104 q = 1) (hb : d208034 q = 1) : d241386 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27104, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27104, d241386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27123 q = 1) (hb : d208034 q = 1) : d241399 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27123, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64713 q ha hb
    | true =>
      simp only [d27123, d241399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64693 q ha hb
  have h9 (q : Pattern) (ha : d202216 q = 1) (hb : d208034 q = 1) : d241400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202216, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202216, d241400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d27210 q = 1) (hb : d208034 q = 1) : d241421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27210, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64719 q ha hb
    | true =>
      simp only [d27210, d241421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d27211 q = 1) (hb : d208034 q = 1) : d241422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27211, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27211, d241422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d202217 q = 1) (hb : d208034 q = 1) : d241423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202217, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d202217, d241423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202218 q = 1) (hb : d208034 q = 1) : d241424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202218, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d202218, d241424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202219 q = 1) (hb : d208034 q = 1) : d241425 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202219, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202219, d241425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27218 q = 1) (hb : d208034 q = 1) : d241429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27218, d241429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64721 q ha hb
    | true =>
      simp only [d27218, d241429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64722 q ha hb
  have h16 (q : Pattern) (ha : d27219 q = 1) (hb : d208034 q = 1) : d241430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27219, d241430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27219, d241430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27220 q = 1) (hb : d208034 q = 1) : d241431 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27220, d241431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d27220, d241431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d27221 q = 1) (hb : d208034 q = 1) : d241432 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d27221, d241432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27221, d241432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d27224 q = 1) (hb : d208034 q = 1) : d241435 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27224, d241435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64723 q ha hb
    | true =>
      simp only [d27224, d241435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64724 q ha hb
  have h20 (q : Pattern) (ha : d27225 q = 1) (hb : d208034 q = 1) : d241436 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27225, d241436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27225, d241436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d27226 q = 1) (hb : d208034 q = 1) : d241437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d27226, d241437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d27226, d241437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d27228 q = 1) (hb : d208034 q = 1) : d241439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27228, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64725 q ha hb
    | true =>
      simp only [d27228, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64696 q ha hb
  have h23 (q : Pattern) (ha : d202221 q = 1) (hb : d208034 q = 1) : d241440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202221, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d27234 q = 1) (hb : d208034 q = 1) : d241442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27234, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64726 q ha hb
    | true =>
      simp only [d27234, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d27235 q = 1) (hb : d208034 q = 1) : d241443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27235, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d27235, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d202222 q = 1) (hb : d208034 q = 1) : d241444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d202222, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d202223 q = 1) (hb : d208034 q = 1) : d241445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202223, d241445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202223, d241445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d202224 q = 1) (hb : d208034 q = 1) : d241446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202224, d241446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d202224, d241446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d202225 q = 1) (hb : d208034 q = 1) : d241447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202225, d241447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202225, d241447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro64728 (p : Pattern) (ha : d202232 p = 1) (hb : d208034 p = 1) : d241467 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27228 q = 1) (hb : d208034 q = 1) : d241439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27228, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64725 q ha hb
    | true =>
      simp only [d27228, d241439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64696 q ha hb
  have h2 (q : Pattern) (ha : d202221 q = 1) (hb : d208034 q = 1) : d241440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202221, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202221, d241440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27234 q = 1) (hb : d208034 q = 1) : d241442 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27234, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64726 q ha hb
    | true =>
      simp only [d27234, d241442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27235 q = 1) (hb : d208034 q = 1) : d241443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27235, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27235, d241443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202222 q = 1) (hb : d208034 q = 1) : d241444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202222, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202222, d241444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202230 q = 1) (hb : d208034 q = 1) : d241465 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202230, d241465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202230, d241465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202231 q = 1) (hb : d208034 q = 1) : d241466 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202231, d241466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202231, d241466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202232 q = 1) (hb : d208034 q = 1) : d241467 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202232, d241467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202232, d241467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64729 (p : Pattern) (ha : d27283 p = 1) (hb : d208034 p = 1) : d241480 p = 1 := by
  have h0 (q : Pattern) (ha : d27276 q = 1) (hb : d208034 q = 1) : d27276 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27275 q = 1) (hb : d208034 q = 1) : d27275 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d27278 q = 1) (hb : d208034 q = 1) : d241475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27278, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27278, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
  have h4 (q : Pattern) (ha : d27026 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
    | true =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d27279 q = 1) (hb : d208034 q = 1) : d241476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27279, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27279, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27027 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d27280 q = 1) (hb : d208034 q = 1) : d241477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27280, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27280, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27281 q = 1) (hb : d208034 q = 1) : d241478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27281, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27281, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d27282 q = 1) (hb : d208034 q = 1) : d241479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27282, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27282, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27283 q = 1) (hb : d208034 q = 1) : d241480 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27283, d241480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27283, d241480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64730 (p : Pattern) (ha : d27288 p = 1) (hb : d208034 p = 1) : d241485 p = 1 := by
  have h0 (q : Pattern) (ha : d27275 q = 1) (hb : d208034 q = 1) : d27275 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27278 q = 1) (hb : d208034 q = 1) : d241475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27278, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27278, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
  have h3 (q : Pattern) (ha : d27026 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64685 q ha hb
    | true =>
      simp only [d27026, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27279 q = 1) (hb : d208034 q = 1) : d241476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27279, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27279, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27027 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27027, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27280 q = 1) (hb : d208034 q = 1) : d241477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27280, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27280, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27281 q = 1) (hb : d208034 q = 1) : d241478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27281, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27281, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27282 q = 1) (hb : d208034 q = 1) : d241479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27282, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27282, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27287 q = 1) (hb : d208034 q = 1) : d241484 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27287, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27287, d241484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d27288 q = 1) (hb : d208034 q = 1) : d241485 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27288, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27288, d241485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro64731 (p : Pattern) (ha : d27309 p = 1) (hb : d208034 p = 1) : d241496 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27277 q = 1) (hb : d208034 q = 1) : d27277 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27284 q = 1) (hb : d208034 q = 1) : d241481 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27284, d241481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27284, d241481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64729 q ha hb
  have h3 (q : Pattern) (ha : d27285 q = 1) (hb : d208034 q = 1) : d241482 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27285, d241482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27285, d241482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27286 q = 1) (hb : d208034 q = 1) : d241483 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27286, d241483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27286, d241483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27289 q = 1) (hb : d208034 q = 1) : d241486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27289, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64729 q ha hb
    | true =>
      simp only [d27289, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64730 q ha hb
  have h6 (q : Pattern) (ha : d27290 q = 1) (hb : d208034 q = 1) : d241487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27290, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27290, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27291 q = 1) (hb : d208034 q = 1) : d241488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27291, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27291, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27292 q = 1) (hb : d208034 q = 1) : d241489 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27292, d241489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27292, d241489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27299 q = 1) (hb : d208034 q = 1) : d241486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27299, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64729 q ha hb
    | true =>
      simp only [d27299, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64702 q ha hb
  have h10 (q : Pattern) (ha : d27300 q = 1) (hb : d208034 q = 1) : d241487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27300, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27300, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27301 q = 1) (hb : d208034 q = 1) : d241488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27301, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27301, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27304 q = 1) (hb : d208034 q = 1) : d241491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64702 q ha hb
    | true =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64703 q ha hb
  have h13 (q : Pattern) (ha : d27305 q = 1) (hb : d208034 q = 1) : d241492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27306 q = 1) (hb : d208034 q = 1) : d241493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d27307 q = 1) (hb : d208034 q = 1) : d241494 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27307, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27307, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d27308 q = 1) (hb : d208034 q = 1) : d241495 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27308, d241495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27308, d241495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d27309 q = 1) (hb : d208034 q = 1) : d241496 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27309, d241496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d27309, d241496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro64732 (p : Pattern) (ha : d27314 p = 1) (hb : d208034 p = 1) : d241501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27299 q = 1) (hb : d208034 q = 1) : d241486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27299, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64729 q ha hb
    | true =>
      simp only [d27299, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64702 q ha hb
  have h2 (q : Pattern) (ha : d27300 q = 1) (hb : d208034 q = 1) : d241487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27300, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27300, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27301 q = 1) (hb : d208034 q = 1) : d241488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27301, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27301, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27304 q = 1) (hb : d208034 q = 1) : d241491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64702 q ha hb
    | true =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64703 q ha hb
  have h5 (q : Pattern) (ha : d27305 q = 1) (hb : d208034 q = 1) : d241492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27306 q = 1) (hb : d208034 q = 1) : d241493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27307 q = 1) (hb : d208034 q = 1) : d241494 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27307, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27307, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27312 q = 1) (hb : d208034 q = 1) : d241499 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27312, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27312, d241499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d27313 q = 1) (hb : d208034 q = 1) : d241500 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27313, d241500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27313, d241500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27314 q = 1) (hb : d208034 q = 1) : d241501 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27314, d241501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27314, d241501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro64733 (p : Pattern) (ha : d27320 p = 1) (hb : d208034 p = 1) : d241507 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27310 q = 1) (hb : d208034 q = 1) : d241497 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27310, d241497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64731 q ha hb
    | true =>
      simp only [d27310, d241497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27311 q = 1) (hb : d208034 q = 1) : d241498 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27311, d241498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27311, d241498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27315 q = 1) (hb : d208034 q = 1) : d241502 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27315, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64732 q ha hb
    | true =>
      simp only [d27315, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27316 q = 1) (hb : d208034 q = 1) : d241503 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27316, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27316, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27317 q = 1) (hb : d208034 q = 1) : d241504 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27317, d241504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27317, d241504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27318 q = 1) (hb : d208034 q = 1) : d241505 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27318, d241505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27318, d241505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27319 q = 1) (hb : d208034 q = 1) : d241506 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27319, d241506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27319, d241506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27320 q = 1) (hb : d208034 q = 1) : d241507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27320, d241507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27320, d241507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64734 (p : Pattern) (ha : d27328 p = 1) (hb : d208034 p = 1) : d241515 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27315 q = 1) (hb : d208034 q = 1) : d241502 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27315, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64732 q ha hb
    | true =>
      simp only [d27315, d241502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27316 q = 1) (hb : d208034 q = 1) : d241503 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27316, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27316, d241503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27323 q = 1) (hb : d208034 q = 1) : d241510 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27323, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64704 q ha hb
    | true =>
      simp only [d27323, d241510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27324 q = 1) (hb : d208034 q = 1) : d241511 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27324, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27324, d241511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27325 q = 1) (hb : d208034 q = 1) : d241512 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27325, d241512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27325, d241512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27326 q = 1) (hb : d208034 q = 1) : d241513 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27326, d241513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27326, d241513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27327 q = 1) (hb : d208034 q = 1) : d241514 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27327, d241514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27327, d241514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27328 q = 1) (hb : d208034 q = 1) : d241515 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27328, d241515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27328, d241515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64735 (p : Pattern) (ha : d27385 p = 1) (hb : d208034 p = 1) : d241523 p = 1 := by
  have h0 (q : Pattern) (ha : d27275 q = 1) (hb : d208034 q = 1) : d27275 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d27293 q = 1) (hb : d208034 q = 1) : d241475 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27293, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27293, d241475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
  have h3 (q : Pattern) (ha : d27036 q = 1) (hb : d208034 q = 1) : d241318 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64687 q ha hb
    | true =>
      simp only [d27036, d241318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d27294 q = 1) (hb : d208034 q = 1) : d241476 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27294, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27294, d241476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d27037 q = 1) (hb : d208034 q = 1) : d241319 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27037, d241319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d27295 q = 1) (hb : d208034 q = 1) : d241477 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27295, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27295, d241477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27296 q = 1) (hb : d208034 q = 1) : d241478 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27296, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27296, d241478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d27297 q = 1) (hb : d208034 q = 1) : d241479 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27297, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27297, d241479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d27380 q = 1) (hb : d208034 q = 1) : d241518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27380, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27380, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64714 q ha hb
  have h10 (q : Pattern) (ha : d27185 q = 1) (hb : d208034 q = 1) : d241402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27185, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64714 q ha hb
    | true =>
      simp only [d27185, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d27381 q = 1) (hb : d208034 q = 1) : d241519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27381, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d27381, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27186 q = 1) (hb : d208034 q = 1) : d241403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27186, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27186, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d27382 q = 1) (hb : d208034 q = 1) : d241520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27382, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27382, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d27383 q = 1) (hb : d208034 q = 1) : d241521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27383, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d27383, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h15 (q : Pattern) (ha : d27384 q = 1) (hb : d208034 q = 1) : d241522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27384, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d27384, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h16 (q : Pattern) (ha : d27385 q = 1) (hb : d208034 q = 1) : d241523 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27385, d241523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27385, d241523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro64736 (p : Pattern) (ha : d27391 p = 1) (hb : d208034 p = 1) : d241524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27386 q = 1) (hb : d208034 q = 1) : d241518 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27386, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27386, d241518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64716 q ha hb
  have h2 (q : Pattern) (ha : d27192 q = 1) (hb : d208034 q = 1) : d241402 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27192, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64716 q ha hb
    | true =>
      simp only [d27192, d241402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27387 q = 1) (hb : d208034 q = 1) : d241519 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27387, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27387, d241519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27193 q = 1) (hb : d208034 q = 1) : d241403 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27193, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27193, d241403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27388 q = 1) (hb : d208034 q = 1) : d241520 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27388, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27388, d241520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27389 q = 1) (hb : d208034 q = 1) : d241521 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27389, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27389, d241521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27390 q = 1) (hb : d208034 q = 1) : d241522 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27390, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27390, d241522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d27391 q = 1) (hb : d208034 q = 1) : d241524 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d27391, d241524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27391, d241524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro64737 (p : Pattern) (ha : d27397 p = 1) (hb : d208034 p = 1) : d241530 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27299 q = 1) (hb : d208034 q = 1) : d241486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27299, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64729 q ha hb
    | true =>
      simp only [d27299, d241486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64702 q ha hb
  have h2 (q : Pattern) (ha : d27300 q = 1) (hb : d208034 q = 1) : d241487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27300, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27300, d241487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27301 q = 1) (hb : d208034 q = 1) : d241488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27301, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27301, d241488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27304 q = 1) (hb : d208034 q = 1) : d241491 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64702 q ha hb
    | true =>
      simp only [d27304, d241491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64703 q ha hb
  have h5 (q : Pattern) (ha : d27305 q = 1) (hb : d208034 q = 1) : d241492 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27305, d241492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27306 q = 1) (hb : d208034 q = 1) : d241493 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27306, d241493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d27307 q = 1) (hb : d208034 q = 1) : d241494 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27307, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27307, d241494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d27392 q = 1) (hb : d208034 q = 1) : d241525 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d27392, d241525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64735 q ha hb
    | true =>
      simp only [d27392, d241525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64736 q ha hb
  have h9 (q : Pattern) (ha : d27393 q = 1) (hb : d208034 q = 1) : d241526 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d27393, d241526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27393, d241526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27394 q = 1) (hb : d208034 q = 1) : d241527 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d27394, d241527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27394, d241527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27395 q = 1) (hb : d208034 q = 1) : d241528 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d27395, d241528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27395, d241528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d27396 q = 1) (hb : d208034 q = 1) : d241529 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d27396, d241529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d27396, d241529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d27397 q = 1) (hb : d208034 q = 1) : d241530 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d27397, d241530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d27397, d241530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro64738 (p : Pattern) (ha : d27403 p = 1) (hb : d208034 p = 1) : d241536 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27398 q = 1) (hb : d208034 q = 1) : d241531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d27398, d241531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64737 q ha hb
    | true =>
      simp only [d27398, d241531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27399 q = 1) (hb : d208034 q = 1) : d241532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d27399, d241532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27399, d241532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d27400 q = 1) (hb : d208034 q = 1) : d241533 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d27400, d241533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27400, d241533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27401 q = 1) (hb : d208034 q = 1) : d241534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d27401, d241534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27401, d241534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27402 q = 1) (hb : d208034 q = 1) : d241535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d27402, d241535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d27402, d241535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d27403 q = 1) (hb : d208034 q = 1) : d241536 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d27403, d241536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27403, d241536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64739 (p : Pattern) (ha : d202242 p = 1) (hb : d208034 p = 1) : d241542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27329 q = 1) (hb : d208034 q = 1) : d241516 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27329, d241516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64733 q ha hb
    | true =>
      simp only [d27329, d241516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64734 q ha hb
  have h2 (q : Pattern) (ha : d202238 q = 1) (hb : d208034 q = 1) : d241517 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d202238, d241517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202238, d241517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27404 q = 1) (hb : d208034 q = 1) : d241537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d27404, d241537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64738 q ha hb
    | true =>
      simp only [d27404, d241537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d27405 q = 1) (hb : d208034 q = 1) : d241538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d27405, d241538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27405, d241538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202239 q = 1) (hb : d208034 q = 1) : d241539 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202239, d241539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202239, d241539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202240 q = 1) (hb : d208034 q = 1) : d241540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d202240, d241540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202240, d241540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202241 q = 1) (hb : d208034 q = 1) : d241541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d202241, d241541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202241, d241541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d202242 q = 1) (hb : d208034 q = 1) : d241542 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d202242, d241542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202242, d241542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro64740 (p : Pattern) (ha : d202248 p = 1) (hb : d208034 p = 1) : d241559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27075 q = 1) (hb : d208034 q = 1) : d241357 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27075, d241357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27075, d241357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64695 q ha hb
  have h2 (q : Pattern) (ha : d27076 q = 1) (hb : d208034 q = 1) : d241358 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27076, d241358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27076, d241358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27085 q = 1) (hb : d208034 q = 1) : d241367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27085, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64695 q ha hb
    | true =>
      simp only [d27085, d241367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64698 q ha hb
  have h4 (q : Pattern) (ha : d27086 q = 1) (hb : d208034 q = 1) : d241368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d27086, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27086, d241368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27087 q = 1) (hb : d208034 q = 1) : d241369 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d27087, d241369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27087, d241369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202226 q = 1) (hb : d208034 q = 1) : d241448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202226, d241448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64720 q ha hb
    | true =>
      simp only [d202226, d241448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64727 q ha hb
  have h7 (q : Pattern) (ha : d27253 q = 1) (hb : d208034 q = 1) : d241461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27253, d241461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64699 q ha hb
    | true =>
      simp only [d27253, d241461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64700 q ha hb
  have h8 (q : Pattern) (ha : d202227 q = 1) (hb : d208034 q = 1) : d241462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202227, d241462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202227, d241462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202228 q = 1) (hb : d208034 q = 1) : d241463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202228, d241463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d202228, d241463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d202229 q = 1) (hb : d208034 q = 1) : d241464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202229, d241464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202229, d241464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202233 q = 1) (hb : d208034 q = 1) : d241468 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202233, d241468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202233, d241468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64728 q ha hb
  have h12 (q : Pattern) (ha : d27262 q = 1) (hb : d208034 q = 1) : d241470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27262, d241470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27262, d241470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64701 q ha hb
  have h13 (q : Pattern) (ha : d202234 q = 1) (hb : d208034 q = 1) : d241471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202234, d241471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d202234, d241471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202235 q = 1) (hb : d208034 q = 1) : d241472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202235, d241472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d202235, d241472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d202236 q = 1) (hb : d208034 q = 1) : d241473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202236, d241473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d202236, d241473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d202237 q = 1) (hb : d208034 q = 1) : d241474 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202237, d241474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202237, d241474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d202243 q = 1) (hb : d208034 q = 1) : d241543 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d202243, d241543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202243, d241543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64739 q ha hb
  have h18 (q : Pattern) (ha : d27421 q = 1) (hb : d208034 q = 1) : d241554 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d27421, d241554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27421, d241554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64706 q ha hb
  have h19 (q : Pattern) (ha : d202244 q = 1) (hb : d208034 q = 1) : d241555 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d202244, d241555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d202244, d241555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d202245 q = 1) (hb : d208034 q = 1) : d241556 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d202245, d241556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d202245, d241556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d202246 q = 1) (hb : d208034 q = 1) : d241557 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d202246, d241557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202246, d241557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d202247 q = 1) (hb : d208034 q = 1) : d241558 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d202247, d241558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d202247, d241558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d202248 q = 1) (hb : d208034 q = 1) : d241559 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d202248, d241559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d202248, d241559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro64741 (p : Pattern) (ha : d202254 p = 1) (hb : d208034 p = 1) : d241565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202249 q = 1) (hb : d208034 q = 1) : d241560 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d202249, d241560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202249, d241560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64740 q ha hb
  have h2 (q : Pattern) (ha : d202250 q = 1) (hb : d208034 q = 1) : d241561 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d202250, d241561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202250, d241561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d202251 q = 1) (hb : d208034 q = 1) : d241562 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d202251, d241562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202251, d241562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202252 q = 1) (hb : d208034 q = 1) : d241563 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d202252, d241563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202252, d241563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d202253 q = 1) (hb : d208034 q = 1) : d241564 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d202253, d241564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202253, d241564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202254 q = 1) (hb : d208034 q = 1) : d241565 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d202254, d241565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202254, d241565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro64742 (p : Pattern) (ha : d202260 p = 1) (hb : d208034 p = 1) : d241571 p = 1 := by
  have h0 (q : Pattern) (ha : d202089 q = 1) (hb : d208034 q = 1) : d240587 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202089, d240587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64472 q ha hb
    | true =>
      simp only [d202089, d240587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64514 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d202129 q = 1) (hb : d208034 q = 1) : d240806 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202129, d240806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202129, d240806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64565 q ha hb
  have h3 (q : Pattern) (ha : d202130 q = 1) (hb : d208034 q = 1) : d240807 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202130, d240807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d202130, d240807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d202170 q = 1) (hb : d208034 q = 1) : d241057 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202170, d241057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202170, d241057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64624 q ha hb
  have h5 (q : Pattern) (ha : d202171 q = 1) (hb : d208034 q = 1) : d241058 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202171, d241058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202171, d241058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d202172 q = 1) (hb : d208034 q = 1) : d241059 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202172, d241059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202172, d241059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d202212 q = 1) (hb : d208034 q = 1) : d241313 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202212, d241313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202212, d241313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64684 q ha hb
  have h8 (q : Pattern) (ha : d202213 q = 1) (hb : d208034 q = 1) : d241314 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202213, d241314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202213, d241314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d202214 q = 1) (hb : d208034 q = 1) : d241315 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202214, d241315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202214, d241315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d202215 q = 1) (hb : d208034 q = 1) : d241316 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202215, d241316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d202215, d241316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d202255 q = 1) (hb : d208034 q = 1) : d241566 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d202255, d241566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202255, d241566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64741 q ha hb
  have h12 (q : Pattern) (ha : d202256 q = 1) (hb : d208034 q = 1) : d241567 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d202256, d241567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202256, d241567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d202257 q = 1) (hb : d208034 q = 1) : d241568 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d202257, d241568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202257, d241568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d202258 q = 1) (hb : d208034 q = 1) : d241569 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d202258, d241569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202258, d241569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d202259 q = 1) (hb : d208034 q = 1) : d241570 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d202259, d241570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d202259, d241570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d202260 q = 1) (hb : d208034 q = 1) : d241571 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d202260, d241571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d202260, d241571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro64743 (p : Pattern) (ha : d202266 p = 1) (hb : d208034 p = 1) : d241577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202261 q = 1) (hb : d208034 q = 1) : d241572 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d202261, d241572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64742 q ha hb
    | true =>
      simp only [d202261, d241572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202262 q = 1) (hb : d208034 q = 1) : d241573 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d202262, d241573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202262, d241573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202263 q = 1) (hb : d208034 q = 1) : d241574 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d202263, d241574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202263, d241574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202264 q = 1) (hb : d208034 q = 1) : d241575 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d202264, d241575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202264, d241575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202265 q = 1) (hb : d208034 q = 1) : d241576 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d202265, d241576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202265, d241576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202266 q = 1) (hb : d208034 q = 1) : d241577 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d202266, d241577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202266, d241577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64744 (p : Pattern) (ha : d202272 p = 1) (hb : d208034 p = 1) : d241583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202267 q = 1) (hb : d208034 q = 1) : d241578 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d202267, d241578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64743 q ha hb
    | true =>
      simp only [d202267, d241578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202268 q = 1) (hb : d208034 q = 1) : d241579 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d202268, d241579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202268, d241579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202269 q = 1) (hb : d208034 q = 1) : d241580 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d202269, d241580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202269, d241580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202270 q = 1) (hb : d208034 q = 1) : d241581 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d202270, d241581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202270, d241581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202271 q = 1) (hb : d208034 q = 1) : d241582 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d202271, d241582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202271, d241582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202272 q = 1) (hb : d208034 q = 1) : d241583 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d202272, d241583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202272, d241583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64745 (p : Pattern) (ha : d202278 p = 1) (hb : d208034 p = 1) : d241589 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202273 q = 1) (hb : d208034 q = 1) : d241584 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d202273, d241584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64744 q ha hb
    | true =>
      simp only [d202273, d241584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202274 q = 1) (hb : d208034 q = 1) : d241585 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d202274, d241585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202274, d241585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202275 q = 1) (hb : d208034 q = 1) : d241586 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d202275, d241586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202275, d241586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202276 q = 1) (hb : d208034 q = 1) : d241587 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d202276, d241587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202276, d241587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202277 q = 1) (hb : d208034 q = 1) : d241588 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d202277, d241588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202277, d241588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202278 q = 1) (hb : d208034 q = 1) : d241589 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d202278, d241589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202278, d241589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64746 (p : Pattern) (ha : d202284 p = 1) (hb : d208034 p = 1) : d241595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202279 q = 1) (hb : d208034 q = 1) : d241590 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d202279, d241590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64745 q ha hb
    | true =>
      simp only [d202279, d241590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202280 q = 1) (hb : d208034 q = 1) : d241591 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d202280, d241591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202280, d241591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202281 q = 1) (hb : d208034 q = 1) : d241592 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d202281, d241592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202281, d241592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202282 q = 1) (hb : d208034 q = 1) : d241593 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d202282, d241593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202282, d241593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202283 q = 1) (hb : d208034 q = 1) : d241594 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d202283, d241594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202283, d241594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202284 q = 1) (hb : d208034 q = 1) : d241595 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d202284, d241595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202284, d241595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64747 (p : Pattern) (ha : d202290 p = 1) (hb : d208034 p = 1) : d241601 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202285 q = 1) (hb : d208034 q = 1) : d241596 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d202285, d241596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64746 q ha hb
    | true =>
      simp only [d202285, d241596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202286 q = 1) (hb : d208034 q = 1) : d241597 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d202286, d241597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202286, d241597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202287 q = 1) (hb : d208034 q = 1) : d241598 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d202287, d241598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202287, d241598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202288 q = 1) (hb : d208034 q = 1) : d241599 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d202288, d241599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202288, d241599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202289 q = 1) (hb : d208034 q = 1) : d241600 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d202289, d241600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202289, d241600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202290 q = 1) (hb : d208034 q = 1) : d241601 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d202290, d241601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202290, d241601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64748 (p : Pattern) (ha : d202296 p = 1) (hb : d208034 p = 1) : d241607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202291 q = 1) (hb : d208034 q = 1) : d241602 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d202291, d241602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64747 q ha hb
    | true =>
      simp only [d202291, d241602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202292 q = 1) (hb : d208034 q = 1) : d241603 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d202292, d241603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202292, d241603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202293 q = 1) (hb : d208034 q = 1) : d241604 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d202293, d241604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202293, d241604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202294 q = 1) (hb : d208034 q = 1) : d241605 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d202294, d241605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202294, d241605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202295 q = 1) (hb : d208034 q = 1) : d241606 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d202295, d241606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202295, d241606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202296 q = 1) (hb : d208034 q = 1) : d241607 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d202296, d241607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202296, d241607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro64749 (p : Pattern) (ha : d202302 p = 1) (hb : d208034 p = 1) : d241613 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d208034 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d202297 q = 1) (hb : d208034 q = 1) : d241608 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d202297, d241608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64748 q ha hb
    | true =>
      simp only [d202297, d241608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d202298 q = 1) (hb : d208034 q = 1) : d241609 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d202298, d241609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d202298, d241609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d202299 q = 1) (hb : d208034 q = 1) : d241610 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d202299, d241610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d202299, d241610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d202300 q = 1) (hb : d208034 q = 1) : d241611 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d202300, d241611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d202300, d241611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d202301 q = 1) (hb : d208034 q = 1) : d241612 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d202301, d241612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d202301, d241612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d202302 q = 1) (hb : d208034 q = 1) : d241613 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d202302, d241613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d202302, d241613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
